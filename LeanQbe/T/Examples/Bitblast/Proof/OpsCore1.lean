/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Bitblast.Proof.OpsCoreHelpers
public import LeanQbe.T.Examples.Bitblast.Src.OpsCore
import LeanQbe.T.Examples.Bitblast.Proof.DriverHelpers
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0HeadStepGuard
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.MemLemmas

/-!
# Bitwise & Carry Adder WP Proofs (`Bitblast.Proof.OpsCore1`)

Proves canonical `Γ`-parametric `Func.wp` theorems for:
- `bv_blast_bin_bitwise_wp`
- `bv_blast_and_wp`
- `bv_blast_or_wp`
- `bv_blast_xor_wp`
- `bv_full_adder_carry_wp`
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Bitblast.Proof

open LeanQbe.T
open LeanQbe.T.Examples.Bitblast.Ref
open LeanQbe.T.Examples.Bitblast.Src.OpsCore

/-! ## Local Array32 Load/Store Rules -/

@[local c0_load] private theorem oc1_load_lits_add {R : Mem 64 → Prop} {m : Mem 64}
    {a : BitVec 64} {off k : BitVec 32} {xs : List (BitVec 32)}
    (h : (array (t := i32) a xs ⋆ R) m)
    (hwrap : off.toNat + k.toNat < 2 ^ 32) (hi : off.toNat + k.toNat < xs.length) :
    loadVal m i32 (a + BitVec.setWidth 64 (off + k) * 4) =
      some (xs[off.toNat + k.toNat]'hi) :=
  ops_load_array32_u32_add_mul4 h hwrap hi

@[local c0_store] private theorem oc1_store_lits_add {R : Mem 64 → Prop} {m : Mem 64}
    {a : BitVec 64} {off k : BitVec 32} {xs : List (BitVec 32)} (v : BitVec 32)
    (h : (array (t := i32) a xs ⋆ R) m)
    (hwrap : off.toNat + k.toNat < 2 ^ 32) (hi : off.toNat + k.toNat < xs.length) :
    storeOk m i32 (a + BitVec.setWidth 64 (off + k) * 4) ∧
      (array (t := i32) a (xs.set (off.toNat + k.toNat) v) ⋆ R)
        (storeMem m i32 (a + BitVec.setWidth 64 (off + k) * 4) v) :=
  ops_store_array32_u32_add_mul4 v h hwrap hi

/-! ## Loop State & Pure Invariant Helpers for `bv_blast_bin_bitwise` -/

private theorem aig_le_refl (g : Ref.Aig) : g ≤ g :=
  ⟨rfl, Nat.le_refl _, fun _ hi => Array.getElem?_eq_getElem hi⟩

private theorem ops_sep5_emp_all {A B C D R : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ (B ⋆ (C ⋆ (D ⋆ (R ⋆ Std.ExtHashMap.emp))))) m) : (A ⋆ B ⋆ C ⋆ D ⋆ R) m :=
  (by simp only [Std.ExtHashMap.sep_emp]; ac_rfl :
    (A ⋆ (B ⋆ (C ⋆ (D ⋆ (R ⋆ Std.ExtHashMap.emp))))) = (A ⋆ B ⋆ C ⋆ D ⋆ R)) ▸ h

private theorem aigFrame_refl (h : BVHdrState) : h.AigFrame h :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl⟩

private structure BitwiseSt where
  j : BitVec 32
  hdr : BVHdrState
  g : Ref.Aig
  aigW : List (BitVec 64)
  htS : List (BitVec 32)
  xs : List (BitVec 32)

private def BitwiseInv (a_off b_off w op : BitVec 32) (hdr0 : BVHdrState) (g0 : Ref.Aig)
    (lits0 : List (BitVec 32)) (st : BitwiseSt) : Prop :=
  st.j.toNat ≤ w.toNat ∧
  hdr0.BlastFrame st.hdr ∧
  st.hdr.lits_len = hdr0.lits_len + w ∧
  st.hdr.oom = 0#32 ∧
  g0 ≤ st.g ∧
  st.g.nodes.size ≤ g0.nodes.size + bitwiseUnitGates op * st.j.toNat ∧
  AigInv st.hdr st.g st.aigW st.htS ∧
  st.xs.length = lits0.length ∧
  (∀ i < hdr0.lits_len.toNat, st.xs.getD i 0#32 = lits0.getD i 0#32) ∧
  SliceAigWf st.hdr.aig_len.toNat st.xs hdr0.lits_len.toNat st.j.toNat ∧
  ∀ i < st.j.toNat, ∀ ρ : Nat → Bool,
    st.g.evalLit ρ (UInt32.ofBitVec (st.xs.getD (hdr0.lits_len.toNat + i) 0#32)) =
      bitwiseOpFn op
        (g0.evalLit ρ (UInt32.ofBitVec (lits0.getD (a_off.toNat + i) 0#32)))
        (g0.evalLit ρ (UInt32.ofBitVec (lits0.getD (b_off.toNat + i) 0#32)))

private def BitwiseGateJoin (h : BitVec 64) (a_off b_off op : BitVec 32)
    (hdr0 : BVHdrState) (st : BitwiseSt)
    (R : Mem 64 → Prop) : Tup Val [i32] → Mem 64 → Prop :=
  fun (ret, ⟨⟩) ml =>
    ∃ hdr' g' aig' ht',
      hdr0.BlastFrame hdr' ∧
      hdr'.lits_len = st.hdr.lits_len ∧
      st.g ≤ g' ∧
      g'.nodes.size ≤ st.g.nodes.size + bitwiseUnitGates op ∧
      AigInv hdr' g' aig' ht' ∧
      (st.hdr.oom ≠ 0#32 → hdr'.oom ≠ 0#32) ∧
      (st.hdr.oom = 0#32 →
        st.g.A + 1 + st.g.nodes.size + bitwiseUnitGates op ≤ st.hdr.aig_cap.toNat →
        st.g.nodes.size + bitwiseUnitGates op ≤ bvMaxGates → hdr'.oom = 0#32) ∧
      (hdr'.oom = 0#32 → (ret >>> 1).toNat < hdr'.aig_len.toNat ∧
        ∀ ρ : Nat → Bool,
          g'.evalLit ρ (UInt32.ofBitVec ret) =
            bitwiseOpFn op
              (st.g.evalLit ρ (UInt32.ofBitVec (st.xs.getD (a_off.toNat + st.j.toNat) 0#32)))
              (st.g.evalLit ρ (UInt32.ofBitVec (st.xs.getD (b_off.toNat + st.j.toNat) 0#32)))) ∧
      (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aig' ⋆
        array (t := i32) hdr'.ht_ptr ht' ⋆ array (t := i32) hdr'.lits_ptr st.xs ⋆ R) ml

private theorem bitwise_gate_branch {Γ : Env} {Q : Post [i32]} {X : XPost} {J : Cont [i32]}
    {nm : Sym} {opFn : Bool → Bool → Bool} {ug : Nat}
    {h : BitVec 64} {a_off b_off w op : BitVec 32} {hdr0 : BVHdrState} {g0 : Ref.Aig}
    {lits0 : List (BitVec 32)} {st : BitwiseSt} {R : Mem 64 → Prop} {m : Mem 64}
    (hFn : ∀ xs m Q X, bvAigBinSpec opFn ug xs m Q X →
      Γ nm [i64, i32, i32] [i32] xs m Q X)
    (hsA : a_off.toNat + w.toNat ≤ hdr0.lits_len.toNat)
    (hsB : b_off.toNat + w.toNat ≤ hdr0.lits_len.toNat)
    (hwfA : SliceAigWf hdr0.aig_len.toNat lits0 a_off.toNat w.toNat)
    (hwfB : SliceAigWf hdr0.aig_len.toNat lits0 b_off.toNat w.toNat)
    (hlen0 : hdr0.aig_len.toNat ≤ st.hdr.aig_len.toNat)
    (hinv : BitwiseInv a_off b_off w op hdr0 g0 lits0 st)
    (hlt : st.j.toNat < w.toNat)
    (hop_fn : opFn = bitwiseOpFn op)
    (hug_le : ug ≤ bitwiseUnitGates op)
    (hm : (bvHdrMem h st.hdr ⋆ array64 st.hdr.aig_ptr st.aigW ⋆
      array (t := i32) st.hdr.ht_ptr st.htS ⋆ array (t := i32) st.hdr.lits_ptr st.xs ⋆ R) m)
    (hJ : ∀ xs ml, BitwiseGateJoin h a_off b_off op hdr0 st R xs ml → J xs ml) :
    wp Γ Q X (.call (as := [i64, i32, i32]) (bs := [i32]) nm
      (Arg.var h, Arg.var (st.xs.getD (a_off.toNat + st.j.toNat) 0#32),
        Arg.var (st.xs.getD (b_off.toNat + st.j.toNat) 0#32), ())
      fun (p : BitVec 32 × Unit) => .jump J (Arg.var p.fst, ())) m := by
  let la := st.xs.getD (a_off.toNat + st.j.toNat) 0#32
  let lb := st.xs.getD (b_off.toNat + st.j.toNat) 0#32
  have hbnd : st.hdr.oom = 0#32 →
      (la >>> 1).toNat < st.hdr.aig_len.toNat ∧ (lb >>> 1).toNat < st.hdr.aig_len.toNat := by
    intro _
    have hpa : la = lits0.getD (a_off.toNat + st.j.toNat) 0#32 :=
      hinv.2.2.2.2.2.2.2.2.1 _ (by omega)
    have hpb : lb = lits0.getD (b_off.toNat + st.j.toNat) 0#32 :=
      hinv.2.2.2.2.2.2.2.2.1 _ (by omega)
    rw [hpa, hpb]
    exact ⟨Nat.lt_of_lt_of_le (hwfA _ hlt) hlen0, Nat.lt_of_lt_of_le (hwfB _ hlt) hlen0⟩
  c0_hcall hFn
  · refine ⟨st.hdr, st.g, st.aigW, st.htS, array (t := i32) st.hdr.lits_ptr st.xs ⋆ R,
      hinv.2.2.2.2.2.2.1, hbnd, ops_sep5_aig_focus hm, ?_⟩
    intro ret hdr' g' aigW' htS' m' hfr hgg' hsz' hinv' hoom' hok' hpost' hm'
    dsimp only [Arg.val]
    c0_hstraight
    refine hJ (ret, ⟨⟩) m' ⟨hdr', g', aigW', htS', hinv.2.1.trans hfr.toBlastFrame,
      hfr.lits_len.trans rfl, hgg', by omega, hinv', hoom', ?_, ?_, ?_⟩
    · intro ho hcap hgmax
      exact hok' ho (by omega) (by omega)
    · intro ho0
      obtain ⟨hrb, hev⟩ := hpost' ho0
      exact ⟨hrb, fun ρ => by rw [← hop_fn]; exact hev ρ⟩
    · have hlp : hdr'.lits_ptr = st.hdr.lits_ptr := hfr.lits_ptr
      rw [hlp]
      exact ops_sep5_aig_unfocus hm'

private theorem bitwiseInv_step {a_off b_off w op : BitVec 32}
    {hdr0 : BVHdrState} {g0 : Ref.Aig} {aig0 : List (BitVec 64)} {ht0 : List (BitVec 32)}
    {lits0 : List (BitVec 32)} {st : BitwiseSt} {hdr' : BVHdrState} {g' : Ref.Aig}
    {aigW' : List (BitVec 64)} {htS' : List (BitVec 32)} {ret : BitVec 32}
    (hsA : a_off.toNat + w.toNat ≤ hdr0.lits_len.toNat)
    (hsB : b_off.toNat + w.toNat ≤ hdr0.lits_len.toNat)
    (hwfA : SliceAigWf hdr0.aig_len.toNat lits0 a_off.toNat w.toNat)
    (hwfB : SliceAigWf hdr0.aig_len.toNat lits0 b_off.toNat w.toNat)
    (hinv0 : AigInv hdr0 g0 aig0 ht0)
    (hinv : BitwiseInv a_off b_off w op hdr0 g0 lits0 st)
    (hlt : st.j.toNat < w.toNat)
    (hfr0' : hdr0.BlastFrame hdr') (hlen' : hdr'.lits_len = st.hdr.lits_len)
    (ho0' : hdr'.oom = 0#32) (hgg' : st.g ≤ g')
    (hsz' : g'.nodes.size ≤ st.g.nodes.size + bitwiseUnitGates op)
    (hinv' : AigInv hdr' g' aigW' htS')
    (hrb : (ret >>> 1).toNat < hdr'.aig_len.toNat)
    (hev : ∀ ρ : Nat → Bool, g'.evalLit ρ (UInt32.ofBitVec ret) = bitwiseOpFn op
      (st.g.evalLit ρ (UInt32.ofBitVec (st.xs.getD (a_off.toNat + st.j.toNat) 0#32)))
      (st.g.evalLit ρ (UInt32.ofBitVec (st.xs.getD (b_off.toNat + st.j.toNat) 0#32))))
    (hi_out : hdr0.lits_len.toNat + st.j.toNat < st.xs.length) :
    (st.j + 1#32).toNat = st.j.toNat + 1 ∧
      BitwiseInv a_off b_off w op hdr0 g0 lits0
        { j := st.j + 1#32, hdr := hdr', g := g', aigW := aigW', htS := htS',
          xs := st.xs.set (hdr0.lits_len.toNat + st.j.toNat) ret } := by
  have hj1 : (st.j + 1#32).toNat = st.j.toNat + 1 := by
    have := w.isLt
    rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
  have hlen_mono : st.hdr.aig_len.toNat ≤ hdr'.aig_len.toNat :=
    aigInv_aigLen_mono hinv.2.2.2.2.2.2.1 hinv' hgg'
  refine ⟨hj1, by dsimp only; omega, hfr0', hlen'.trans hinv.2.2.1, ho0',
    Ref.Aig.extends_trans hinv.2.2.2.2.1 hgg',
    by dsimp only; have := hinv.2.2.2.2.2.1; rw [hj1, Nat.mul_succ]; omega, hinv',
    by simp [hinv.2.2.2.2.2.2.2.1], ?_, ?_, ?_⟩
  · intro i hi; rw [list_getD_set_ne st.xs 0#32 _ (by omega)]; exact hinv.2.2.2.2.2.2.2.2.1 i hi
  · intro i hi
    by_cases hie : i = st.j.toNat
    · subst hie; rw [list_getD_set_self st.xs 0#32 _ hi_out]; exact hrb
    · rw [list_getD_set_ne st.xs 0#32 _ (by omega)]
      exact Nat.lt_of_lt_of_le (hinv.2.2.2.2.2.2.2.2.2.1 i (by dsimp only at hi; omega)) hlen_mono
  · intro i hi ρ
    by_cases hie : i = st.j.toNat
    · subst hie
      rw [list_getD_set_self st.xs 0#32 _ hi_out, hev ρ]
      have hpa : st.xs.getD (a_off.toNat + st.j.toNat) 0#32 =
          lits0.getD (a_off.toNat + st.j.toNat) 0#32 :=
        hinv.2.2.2.2.2.2.2.2.1 _ (by omega)
      have hpb : st.xs.getD (b_off.toNat + st.j.toNat) 0#32 =
          lits0.getD (b_off.toNat + st.j.toNat) 0#32 :=
        hinv.2.2.2.2.2.2.2.2.1 _ (by omega)
      have heva0 := sliceAigWf_evalLit_extend hinv0 hinv.2.2.2.2.1 hwfA ρ hlt
      have hevb0 := sliceAigWf_evalLit_extend hinv0 hinv.2.2.2.2.1 hwfB ρ hlt
      rw [hpa, hpb, heva0, hevb0]
    · rw [list_getD_set_ne st.xs 0#32 _ (by omega)]
      have hlt_i : i < st.j.toNat := by dsimp only at hi; omega
      have hext := sliceAigWf_evalLit_extend hinv.2.2.2.2.2.2.1 hgg'
        hinv.2.2.2.2.2.2.2.2.2.1 (off := hdr0.lits_len.toNat) ρ hlt_i
      rw [hext]
      exact hinv.2.2.2.2.2.2.2.2.2.2 i hlt_i ρ

/-! ## 1. `bv_blast_bin_bitwise_wp` & `bv_blast_{and,or,xor}_wp` -/

public section

theorem bv_blast_bin_bitwise_wp (Γ : Env)
    (hSliceOk : ∀ xs m Q X, bvSliceOkSpec xs m Q X →
      Γ "bv_slice_ok" [i64, i32, i32] [.bool] xs m Q X)
    (hLitsAlloc : ∀ xs m Q X, bvLitsAllocSpec xs m Q X →
      Γ "bv_lits_alloc" [i64, i32] [i32] xs m Q X)
    (hMkAnd : ∀ xs m Q X, bvMkAndSpec xs m Q X →
      Γ "bv_mk_and" [i64, i32, i32] [i32] xs m Q X)
    (hAigOr : ∀ xs m Q X, bvAigOrSpec xs m Q X →
      Γ "bv_aig_or" [i64, i32, i32] [i32] xs m Q X)
    (hAigXor : ∀ xs m Q X, bvAigXorSpec xs m Q X →
      Γ "bv_aig_xor" [i64, i32, i32] [i32] xs m Q X) :
    ∀ xs m Q X, bvBlastBinBitwiseSpec xs m Q X →
      Func.wp Γ bv_blast_bin_bitwise_body xs m Q X := by
  rintro ⟨h, a_off, b_off, w, op, ⟨⟩⟩ m Q X
    ⟨hdr, g, aigW, htS, lits0, R, hinv0, hlits_cap, hwf, hm, hQ⟩
  refine wp_join_group (ts := []) (fun _ ml => ml = m ∧ bitwiseOpValid op = true)
    (fun _ _ ml ⟨hml, hop⟩ => by
      subst hml
      refine wp_join_group (ts := [])
        (fun _ ml2 => ml2 = ml ∧ ¬ (hdr.oom = 0#32 ∧
          sliceBoundsOk hdr a_off w = true ∧ sliceBoundsOk hdr b_off w = true))
        (fun _ _ ml2 ⟨hml2, hfail⟩ => by
          subst hml2; dsimp only [Blocks.get_here]
          c0_hstraight
          let hdr' : BVHdrState := { hdr with oom := (1 : BitVec 32) }
          have hfr : hdr.BlastFrame hdr' :=
            ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
              rfl, rfl, rfl, rfl, rfl, rfl⟩
          exact hQ 0xFFFFFFFF#32 hdr' g aigW htS lits0 _ hfr (aig_le_refl g)
            (Nat.le_add_right _ _) (aigInv_set_oom (1 : BitVec 32) hinv0) rfl (fun _ _ => rfl)
            (Nat.le_refl _) (Nat.le_add_right _ _) (fun _ => by simp [hdr'])
            (fun h0 _ h1 h2 _ _ _ => False.elim (hfail ⟨h0, h1, h2⟩))
            (fun h0 => False.elim (by simp [hdr'] at h0)) (fun _ => rfl)
            (ops_sep5_emp_all hm))
        (fun J2 hJ2 => by
          c0_hstraight
          c0_hsplit
          · exact hJ2 () ml ⟨rfl, fun ⟨h0, _⟩ => hc h0⟩
          · have h0 : hdr.oom = 0#32 := by bv_omega
            clear hc
            c0_hcall hSliceOk
            · refine ⟨hdr, array64 hdr.aig_ptr aigW ⋆ array (t := i32) hdr.ht_ptr htS ⋆
                  array (t := i32) hdr.lits_ptr lits0 ⋆ R, ops_sep5_hdr_focus hm, ?_⟩
              dsimp only [Arg.val]
              c0_hsplit
              · have hsA : sliceBoundsOk hdr a_off w = true := hc
                obtain ⟨hsA_cap, _, hsA_sum⟩ := sliceBoundsOk_sum hsA
                clear hc
                c0_hcall hSliceOk
                · refine ⟨hdr, array64 hdr.aig_ptr aigW ⋆ array (t := i32) hdr.ht_ptr htS ⋆
                      array (t := i32) hdr.lits_ptr lits0 ⋆ R, ops_sep5_hdr_focus hm, ?_⟩
                  dsimp only [Arg.val]
                  c0_hsplit
                  · have hsB : sliceBoundsOk hdr b_off w = true := hc
                    obtain ⟨_, _, hsB_sum⟩ := sliceBoundsOk_sum hsB
                    clear hc
                    obtain ⟨hwfA, hwfB⟩ := hwf h0 hop hsA hsB
                    c0_hcall hLitsAlloc
                    · refine ⟨hdr, array64 hdr.aig_ptr aigW ⋆ array (t := i32) hdr.ht_ptr htS ⋆
                          array (t := i32) hdr.lits_ptr lits0 ⋆ R, ops_sep5_hdr_focus hm, ?_⟩
                      dsimp only [Arg.val]
                      split
                      · next hroom =>
                        intro m1 hm1
                        obtain ⟨_, _, hroom'⟩ := hroom
                        let hdr1 : BVHdrState := { hdr with lits_len := hdr.lits_len + w }
                        have hm1' : (bvHdrMem h hdr1 ⋆ array64 hdr1.aig_ptr aigW ⋆
                            array (t := i32) hdr1.ht_ptr htS ⋆
                            array (t := i32) hdr1.lits_ptr lits0 ⋆ R) m1 :=
                          ops_sep5_hdr_unfocus hm1
                        c0_hstraight
                        c0_hsplit
                        · exfalso; exact hc h0
                        · c0_hstraight
                          have hfr1 : hdr.BlastFrame hdr1 :=
                            ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                              rfl, rfl, rfl, rfl, rfl, rfl⟩
                          have hinv1 := aigInv_set_litsLen (hdr.lits_len + w) hinv0
                          refine wp_while_record
                            (proj := fun st : BitwiseSt => (st.j, ⟨⟩))
                            (μ := fun st => w.toNat - st.j.toNat)
                            (Inv := BitwiseInv a_off b_off w op hdr g lits0)
                            (MemPred := fun st => bvHdrMem h st.hdr ⋆
                              array64 st.hdr.aig_ptr st.aigW ⋆
                              array (t := i32) st.hdr.ht_ptr st.htS ⋆
                              array (t := i32) st.hdr.lits_ptr st.xs)
                            (R := R)
                            (fun Jw hJw => by
                              c0_hstraight
                              have hz : (0#32 : BitVec 32).toNat = 0 := rfl
                              exact hJw ⟨0#32, hdr1, g, aigW, htS, lits0⟩ m1
                                ⟨by dsimp only; rw [hz]; omega, hfr1, rfl, h0, aig_le_refl g,
                                  by dsimp only; rw [hz]; omega, hinv1, rfl, fun _ _ => rfl,
                                  fun i hi => by dsimp only at hi; rw [hz] at hi; omega,
                                  fun i hi => by dsimp only at hi; rw [hz] at hi; omega⟩ hm1')
                            (fun Jw st ml3 hinv hml3 hrec => by
                              dsimp only [Blocks.get_here] at *
                              c0_hstraight
                              c0_hsplit
                              · have hlt : st.j.toNat < w.toNat := hc
                                clear hc
                                have hwa : a_off.toNat + st.j.toNat < 2 ^ 32 := by
                                  have := hdr.lits_len.isLt; omega
                                have hia : a_off.toNat + st.j.toNat < st.xs.length := by
                                  have := hinv.2.2.2.2.2.2.2.1; omega
                                have hwb : b_off.toNat + st.j.toNat < 2 ^ 32 := by
                                  have := hdr.lits_len.isLt; omega
                                have hib : b_off.toNat + st.j.toNat < st.xs.length := by
                                  have := hinv.2.2.2.2.2.2.2.1; omega
                                have hwo : hdr.lits_len.toNat + st.j.toNat < 2 ^ 32 := by
                                  have := hdr.lits_cap.isLt; omega
                                have hio : hdr.lits_len.toNat + st.j.toNat < st.xs.length := by
                                  have := hinv.2.2.2.2.2.2.2.1; omega
                                have hml3_l : (array (t := i32) hdr.lits_ptr st.xs ⋆
                                    (bvHdrMem h st.hdr ⋆ array64 st.hdr.aig_ptr st.aigW ⋆
                                      array (t := i32) st.hdr.ht_ptr st.htS ⋆ R)) ml3 := by
                                  have h0l := ops_sep5_lits_focus hml3
                                  rwa [hinv.2.1.lits_ptr] at h0l
                                c0_hstraight
                                have hml3_r : (bvHdrMem h st.hdr ⋆ array64 st.hdr.aig_ptr st.aigW ⋆
                                    array (t := i32) st.hdr.ht_ptr st.htS ⋆
                                    array (t := i32) st.hdr.lits_ptr st.xs ⋆ R) ml3 := by
                                  rw [← hinv.2.1.lits_ptr] at hml3_l
                                  exact ops_sep5_lits_unfocus hml3_l
                                rw [ops_list_getElem_eq_getD st.xs 0#32 _
                                    (ops_setWidth64_add_u32 hwa),
                                  ops_list_getElem_eq_getD st.xs 0#32 _
                                    (ops_setWidth64_add_u32 hwb)]
                                refine wp_join_group
                                  (BitwiseGateJoin h a_off b_off op hdr st R)
                                  (fun Jg ⟨g_res, ⟨⟩⟩ ml4 ⟨hdr4, g4, aig4, ht4, hfr04, hlen4,
                                      hgg4, hsz4, hinv4, _, hok4, hpost4, hml4⟩ => by
                                    dsimp only [Blocks.get_here] at *
                                    c0_hstraight
                                    c0_hsplit
                                    · have hne4 : hdr4.oom ≠ 0#32 := hc
                                      clear hc
                                      c0_hstraight
                                      have hlen_le : hdr.lits_len.toNat ≤ hdr4.lits_len.toNat := by
                                        have := hdr.lits_cap.isLt
                                        rw [hlen4, hinv.2.2.1, BitVec.toNat_add,
                                          Nat.mod_eq_of_lt (by omega)]
                                        omega
                                      have hlen_sum :
                                          hdr4.lits_len.toNat ≤ hdr.lits_len.toNat + w.toNat := by
                                        rw [hlen4, hinv.2.2.1, BitVec.toNat_add]
                                        exact Nat.mod_le _ _
                                      have hmul_le : bitwiseUnitGates op * (st.j.toNat + 1) ≤
                                          bitwiseUnitGates op * w.toNat :=
                                        Nat.mul_le_mul_left _ (by omega)
                                      rw [Nat.mul_succ] at hmul_le
                                      refine hQ 0xFFFFFFFF#32 hdr4 g4 aig4 ht4 st.xs ml4 hfr04
                                        (Ref.Aig.extends_trans hinv.2.2.2.2.1 hgg4)
                                        (by have := hinv.2.2.2.2.2.1; omega) hinv4
                                        hinv.2.2.2.2.2.2.2.1 hinv.2.2.2.2.2.2.2.2.1 hlen_le
                                        hlen_sum (fun _ => hne4) ?_
                                        (fun h0' => absurd h0' hne4) (fun _ => rfl) hml4
                                      intro _ _ _ _ _ haig_cap hmaxg
                                      apply hok4 hinv.2.2.2.1
                                      · rw [← hinv.2.2.2.2.1.1, hinv.2.1.aig_cap]
                                        have := hinv.2.2.2.2.2.1; omega
                                      · have := hinv.2.2.2.2.2.1; omega
                                    · have hoom04 : hdr4.oom = 0#32 := by bv_omega
                                      clear hc
                                      have hml4_l : (array (t := i32) hdr.lits_ptr st.xs ⋆
                                          (bvHdrMem h hdr4 ⋆ array64 hdr4.aig_ptr aig4 ⋆
                                            array (t := i32) hdr4.ht_ptr ht4 ⋆ R)) ml4 := by
                                        have h0l := ops_sep5_lits_focus hml4
                                        rwa [hfr04.lits_ptr] at h0l
                                      c0_hstraight
                                      have hm' : (bvHdrMem h hdr4 ⋆ array64 hdr4.aig_ptr aig4 ⋆
                                          array (t := i32) hdr4.ht_ptr ht4 ⋆
                                          array (t := i32) hdr4.lits_ptr
                                            (st.xs.set (hdr.lits_len.toNat + st.j.toNat) g_res) ⋆
                                          R) m := by
                                        rw [← hfr04.lits_ptr] at hm
                                        rw [ops_setWidth64_add_u32 hwo] at hm
                                        exact ops_sep5_lits_unfocus hm
                                      obtain ⟨hrb4, hev4⟩ := hpost4 hoom04
                                      obtain ⟨hj1, hinv'⟩ := bitwiseInv_step hsA_sum hsB_sum hwfA
                                        hwfB hinv0 hinv hlt hfr04 hlen4 hoom04 hgg4 hsz4 hinv4
                                        hrb4 hev4 hio
                                      exact hrec ⟨st.j + 1#32, hdr4, g4, aig4, ht4,
                                          st.xs.set (hdr.lits_len.toNat + st.j.toNat) g_res⟩ m
                                        (by dsimp only; omega) hinv' hm')
                                  (fun Jg hJg => by
                                    have hlen0 := aigInv_aigLen_mono hinv0 hinv.2.2.2.2.2.2.1
                                      hinv.2.2.2.2.1
                                    c0_hstraight
                                    c0_hsplit
                                    · have hop3 : op = 3#32 := hc
                                      exact bitwise_gate_branch hMkAnd hsA_sum hsB_sum hwfA hwfB
                                        hlen0 hinv hlt (by rw [hop3]; rfl)
                                        (by rw [hop3]; simp [bitwiseUnitGates]) hml3_r hJg
                                    · have hne3 : op ≠ 3#32 := by bv_omega
                                      clear hc
                                      refine wp_join_group
                                        (BitwiseGateJoin h a_off b_off op hdr st R)
                                        (fun Jg2 ⟨g_r2, ⟨⟩⟩ ml4 h4 => by
                                          dsimp only [Blocks.get_here]
                                          c0_hstraight
                                          exact hJg (g_r2, ⟨⟩) ml4 h4)
                                        (fun Jg2 hJg2 => by
                                          c0_hstraight
                                          c0_hsplit
                                          · have hop4 : op = 4#32 := hc
                                            exact bitwise_gate_branch hAigOr hsA_sum hsB_sum
                                              hwfA hwfB hlen0 hinv hlt (by rw [hop4]; rfl)
                                              (by rw [hop4]; simp [bitwiseUnitGates]) hml3_r hJg2
                                          · have hne4 : op ≠ 4#32 := by bv_omega
                                            have hop5 : op = 5#32 := by
                                              have := hop
                                              simp only [bitwiseOpValid, decide_eq_true_eq] at this
                                              rcases this with rfl | rfl | rfl
                                              · exact absurd rfl hne3
                                              · exact absurd rfl hne4
                                              · rfl
                                            exact bitwise_gate_branch hAigXor hsA_sum hsB_sum
                                              hwfA hwfB hlen0 hinv hlt (by rw [hop5]; rfl)
                                              (by rw [hop5]; simp [bitwiseUnitGates]) hml3_r hJg2))
                              · have hge : w.toNat ≤ st.j.toNat := by bv_omega
                                have heq : st.j.toNat = w.toNat := by have := hinv.1; omega
                                c0_hstraight
                                have hlen_le : hdr.lits_len.toNat ≤ st.hdr.lits_len.toNat := by
                                  have := hdr.lits_cap.isLt
                                  rw [hinv.2.2.1, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
                                  omega
                                have hlen_sum :
                                    st.hdr.lits_len.toNat ≤ hdr.lits_len.toNat + w.toNat := by
                                  rw [hinv.2.2.1, BitVec.toNat_add]; exact Nat.mod_le _ _
                                refine hQ hdr.lits_len st.hdr st.g st.aigW st.htS st.xs ml3
                                  hinv.2.1 hinv.2.2.2.2.1 (heq ▸ hinv.2.2.2.2.2.1)
                                  hinv.2.2.2.2.2.2.1 hinv.2.2.2.2.2.2.2.1
                                  hinv.2.2.2.2.2.2.2.2.1 hlen_le hlen_sum
                                  (fun hne => absurd h0 hne) (fun _ _ _ _ _ _ _ => hinv.2.2.2.1)
                                  ?_ (fun hne => absurd hinv.2.2.2.1 hne) hml3
                                intro _
                                exact ⟨h0, hop, hsA, hsB, hroom', rfl, hinv.2.2.1,
                                  heq ▸ hinv.2.2.2.2.2.2.2.2.2.1,
                                  fun i hi => hinv.2.2.2.2.2.2.2.2.2.2 i (heq ▸ hi)⟩)
                      · next hnroom =>
                        intro m1 hm1
                        let hdr1 : BVHdrState :=
                          { hdr with oom := if hdr.oom ≠ 0#32 then hdr.oom else 1#32 }
                        have hoom1 : hdr1.oom = 1#32 := by simp [hdr1, h0]
                        have hfr1 : hdr.BlastFrame hdr1 :=
                          ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                            rfl, rfl, rfl, rfl, rfl, rfl⟩
                        c0_hstraight
                        c0_hsplit
                        · c0_hstraight
                          exact hQ 0xFFFFFFFF#32 hdr1 g aigW htS lits0 m1 hfr1
                            (aig_le_refl g) (Nat.le_add_right _ _)
                            (aigInv_set_oom _ hinv0) rfl (fun _ _ => rfl) (Nat.le_refl _)
                            (Nat.le_add_right _ _) (fun hne => absurd h0 hne)
                            (fun _ _ _ _ hr _ _ => False.elim (hnroom ⟨h0, hsA_cap, hr⟩))
                            (fun h0' => absurd h0' (by rw [hoom1]; decide)) (fun _ => rfl)
                            (ops_sep5_hdr_unfocus hm1)
                        · exfalso; simp [h0] at hc
                  · exact hJ2 () ml ⟨rfl, fun ⟨_, _, hs⟩ => by simp [hs] at hc⟩
              · exact hJ2 () ml ⟨rfl, fun ⟨_, hs, _⟩ => by simp [hs] at hc⟩))
    (fun J1 hJ1 => by
      c0_hstraight
      c0_hsplit
      · have hne3 : op ≠ 3#32 := hc; clear hc
        c0_hstraight
        c0_hsplit
        · have hne4 : op ≠ 4#32 := hc; clear hc
          c0_hstraight
          c0_hsplit
          · have hne5 : op ≠ 5#32 := hc; clear hc
            c0_hstraight
            let hdr' : BVHdrState := { hdr with oom := (1 : BitVec 32) }
            have hfr : hdr.BlastFrame hdr' :=
              ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                rfl, rfl, rfl, rfl, rfl, rfl⟩
            have hinv_bad : bitwiseOpValid op = false := by
              simp only [bitwiseOpValid, decide_eq_false_iff_not]
              rintro (rfl | rfl | rfl) <;> contradiction
            exact hQ 0xFFFFFFFF#32 hdr' g aigW htS lits0 _ hfr (aig_le_refl g)
              (Nat.le_add_right _ _) (aigInv_set_oom (1 : BitVec 32) hinv0) rfl
              (fun _ _ => rfl) (Nat.le_refl _) (Nat.le_add_right _ _)
              (fun _ => by simp [hdr']) (fun _ hv => by rw [hinv_bad] at hv; cases hv)
              (fun h0 => False.elim (by simp [hdr'] at h0)) (fun _ => rfl)
              (ops_sep5_emp_all hm)
          · have heq5 : op = 5#32 := by bv_omega
            have hv : bitwiseOpValid op = true := by simp [bitwiseOpValid, heq5]
            exact hJ1 () m ⟨rfl, hv⟩
        · have heq4 : op = 4#32 := by bv_omega
          have hv : bitwiseOpValid op = true := by simp [bitwiseOpValid, heq4]
          exact hJ1 () m ⟨rfl, hv⟩
      · have heq3 : op = 3#32 := by bv_omega
        have hv : bitwiseOpValid op = true := by simp [bitwiseOpValid, heq3]
        exact hJ1 () m ⟨rfl, hv⟩)

end

private theorem bitwise_spec_adapter {op : BitVec 32} {opFn : Bool → Bool → Bool} {ug : Nat}
    (hopv : bitwiseOpValid op = true) (hfn : bitwiseOpFn op = opFn)
    (hug : bitwiseUnitGates op = ug)
    {xs : Tup Val [i64, i32, i32, i32]} {m : Mem 64} {Q : Post [i32]} {X : XPost}
    (hspec : bvBlastBitwiseSpec opFn ug xs m Q X) :
    bvBlastBinBitwiseSpec (xs.1, xs.2.1, xs.2.2.1, xs.2.2.2.1, op, ⟨⟩) m Q X := by
  rcases xs with ⟨h, a_off, b_off, w, ⟨⟩⟩
  rcases hspec with ⟨hdr, g, aigW, htS, lits0, R, hinv0, hlits_cap, hwf, hm, hQ⟩
  refine ⟨hdr, g, aigW, htS, lits0, R, hinv0, hlits_cap, fun h0 _ => hwf h0, hm, ?_⟩
  intro ret hdr' g' aigW' htS' lits' m' hfr hgg hsz hinv' hlen hpref hle hsum hne hok hpost hoom
    hm'
  rw [hug] at hsz
  refine hQ ret hdr' g' aigW' htS' lits' m' hfr hgg hsz hinv' hlen hpref hle hsum hne
    (fun h0 hsA hsB hroom hcap hmaxg => hok h0 hopv hsA hsB hroom (hug ▸ hcap) (hug ▸ hmaxg))
    ?_ hoom hm'
  intro ho0
  obtain ⟨h0, _, hsA, hsB, hroom, hr, hl, hwf', hev⟩ := hpost ho0
  exact ⟨h0, hsA, hsB, hroom, hr, hl, hwf', fun j hj ρ => by rw [← hfn]; exact hev j hj ρ⟩

public section

theorem bv_blast_and_wp (Γ : Env)
    (hBin : ∀ xs m Q X, bvBlastBinBitwiseSpec xs m Q X →
      Γ "bv_blast_bin_bitwise" [i64, i32, i32, i32, i32] [i32] xs m Q X) :
    ∀ xs m Q X, bvBlastAndSpec xs m Q X → Func.wp Γ bv_blast_and_body xs m Q X := by
  rintro ⟨h, a_off, b_off, w, ⟨⟩⟩ m Q X hspec
  c0_hstraight
  c0_hcall hBin
  exact bitwise_spec_adapter (op := 3#32) (by decide) rfl rfl hspec

theorem bv_blast_or_wp (Γ : Env)
    (hBin : ∀ xs m Q X, bvBlastBinBitwiseSpec xs m Q X →
      Γ "bv_blast_bin_bitwise" [i64, i32, i32, i32, i32] [i32] xs m Q X) :
    ∀ xs m Q X, bvBlastOrSpec xs m Q X → Func.wp Γ bv_blast_or_body xs m Q X := by
  rintro ⟨h, a_off, b_off, w, ⟨⟩⟩ m Q X hspec
  c0_hstraight
  c0_hcall hBin
  exact bitwise_spec_adapter (op := 4#32) (by decide) rfl rfl hspec

theorem bv_blast_xor_wp (Γ : Env)
    (hBin : ∀ xs m Q X, bvBlastBinBitwiseSpec xs m Q X →
      Γ "bv_blast_bin_bitwise" [i64, i32, i32, i32, i32] [i32] xs m Q X) :
    ∀ xs m Q X, bvBlastXorSpec xs m Q X → Func.wp Γ bv_blast_xor_body xs m Q X := by
  rintro ⟨h, a_off, b_off, w, ⟨⟩⟩ m Q X hspec
  c0_hstraight
  c0_hcall hBin
  exact bitwise_spec_adapter (op := 5#32) (by decide) rfl rfl hspec

end

private theorem fac_oom_exit {h : BitVec 64} {a b cin : BitVec 32}
    {hdr hdr1 : BVHdrState} {g g1 : Ref.Aig} {aig1 : List (BitVec 64)} {ht1 : List (BitVec 32)}
    {m1 : Mem 64} {R : Mem 64 → Prop} {Q : (BitVec 32 × PUnit) → Mem 64 → Prop} {k : Nat}
    (hk6 : k ≤ 6) (hfr : hdr.AigFrame hdr1) (hgg : g ≤ g1)
    (hsz : g1.nodes.size ≤ g.nodes.size + k) (hinv1 : AigInv hdr1 g1 aig1 ht1)
    (hne : hdr1.oom ≠ 0#32)
    (hok : hdr.oom = 0#32 → g.A + 1 + g.nodes.size + k ≤ hdr.aig_cap.toNat →
      g.nodes.size + k ≤ bvMaxGates → hdr1.oom = 0#32)
    (hm1 : (bvHdrMem h hdr1 ⋆ array64 hdr1.aig_ptr aig1 ⋆
      array (t := i32) hdr1.ht_ptr ht1 ⋆ R) m1)
    (hQ : ∀ (ret : BitVec 32) (hdr' : BVHdrState) (g' : Ref.Aig) (aig' : List (BitVec 64))
      (ht' : List (BitVec 32)) (m' : Mem 64),
      hdr.AigFrame hdr' → g ≤ g' → g'.nodes.size ≤ g.nodes.size + 6 →
      AigInv hdr' g' aig' ht' → (hdr.oom ≠ 0#32 → hdr'.oom ≠ 0#32) →
      (hdr.oom = 0#32 → g.A + 1 + g.nodes.size + 6 ≤ hdr.aig_cap.toNat →
        g.nodes.size + 6 ≤ bvMaxGates → hdr'.oom = 0#32) →
      (hdr'.oom = 0#32 → hdr.oom = 0#32 ∧ (ret >>> 1).toNat < hdr'.aig_len.toNat ∧
        ∀ ρ : Nat → Bool, g'.evalLit ρ (UInt32.ofBitVec ret) =
          (g.evalLit ρ (UInt32.ofBitVec a)).atLeastTwo
            (g.evalLit ρ (UInt32.ofBitVec b)) (g.evalLit ρ (UInt32.ofBitVec cin))) →
      (hdr'.oom ≠ 0#32 → ret = 0#32) →
      (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aig' ⋆
        array (t := i32) hdr'.ht_ptr ht' ⋆ R) m' → Q (ret, ⟨⟩) m') :
    Q (0#32, ⟨⟩) m1 :=
  hQ 0#32 hdr1 g1 aig1 ht1 m1 hfr hgg (by omega) hinv1 (fun _ => hne)
    (fun h0 hcap hgmax => hok h0 (by omega) (by omega))
    (fun h0' => absurd h0' hne) (fun _ => rfl) hm1

public section

theorem bv_full_adder_carry_wp (Γ : Env)
    (hMkAnd : ∀ xs m Q X, bvMkAndSpec xs m Q X →
      Γ "bv_mk_and" [i64, i32, i32] [i32] xs m Q X)
    (hAigOr : ∀ xs m Q X, bvAigOrSpec xs m Q X →
      Γ "bv_aig_or" [i64, i32, i32] [i32] xs m Q X)
    (hAigXor : ∀ xs m Q X, bvAigXorSpec xs m Q X →
      Γ "bv_aig_xor" [i64, i32, i32] [i32] xs m Q X) :
    ∀ xs m Q X, bvFullAdderCarrySpec xs m Q X →
      Func.wp Γ bv_full_adder_carry_body xs m Q X := by
  rintro ⟨h, a, b, cin, ⟨⟩⟩ m Q X ⟨hdr, g, aigW, htS, R, hinv0, hbnd, hm, hQ⟩
  c0_hstraight
  c0_hsplit
  · c0_hstraight
    exact hQ 0#32 hdr g aigW htS m (aigFrame_refl hdr) (aig_le_refl g)
      (Nat.le_add_right _ _) hinv0 (fun hne => hne) (fun h0 _ _ => absurd h0 hc)
      (fun h0 => absurd h0 hc) (fun _ => rfl) hm
  · have h0 : hdr.oom = 0#32 := by bv_omega
    clear hc
    obtain ⟨ha0, hb0, hc0⟩ := hbnd h0
    c0_hcall hAigXor
    · refine ⟨hdr, g, aigW, htS, R, hinv0, fun _ => ⟨ha0, hb0⟩, hm, ?_⟩
      intro p1 hdr1 g1 aig1 ht1 m1 hfr1 hgg1 hsz1 hinv1 _ hok1 hpost1 hm1
      dsimp only [Arg.val]
      c0_hstraight
      c0_hsplit
      · c0_hstraight
        exact fac_oom_exit (k := 3) (by decide) hfr1 hgg1 hsz1 hinv1 hc hok1 hm1 hQ
      · have h01 : hdr1.oom = 0#32 := by bv_omega
        clear hc
        obtain ⟨hp1_lt, hp1_ev⟩ := hpost1 h01
        have hlen1 := aigInv_aigLen_mono hinv0 hinv1 hgg1
        c0_hcall hMkAnd
        · refine ⟨hdr1, g1, aig1, ht1, R, hinv1,
            fun _ => ⟨hp1_lt, Nat.lt_of_lt_of_le hc0 hlen1⟩, hm1, ?_⟩
          intro c2 hdr2 g2 aig2 ht2 m2 hfr2 hgg2 hsz2 hinv2 _ hok2 hpost2 hm2
          dsimp only [Arg.val]
          c0_hstraight
          c0_hsplit
          · c0_hstraight
            refine fac_oom_exit (k := 4) (by decide) (hfr1.trans hfr2)
              (Ref.Aig.extends_trans hgg1 hgg2) (by omega) hinv2 hc
              (fun _ hcap hmaxg => ?_) hm2 hQ
            apply hok2 h01
            · rw [← hgg1.1, hfr1.aig_cap]; omega
            · omega
          · have h02 : hdr2.oom = 0#32 := by bv_omega
            clear hc
            obtain ⟨hc2_lt, hc2_ev⟩ := hpost2 h02
            have hlen2 := aigInv_aigLen_mono hinv1 hinv2 hgg2
            c0_hcall hMkAnd
            · refine ⟨hdr2, g2, aig2, ht2, R, hinv2,
                fun _ => ⟨Nat.lt_of_lt_of_le ha0 (Nat.le_trans hlen1 hlen2),
                  Nat.lt_of_lt_of_le hb0 (Nat.le_trans hlen1 hlen2)⟩, hm2, ?_⟩
              intro c1 hdr3 g3 aig3 ht3 m3 hfr3 hgg3 hsz3 hinv3 _ hok3 hpost3 hm3
              dsimp only [Arg.val]
              c0_hstraight
              c0_hsplit
              · c0_hstraight
                have hgg12 := Ref.Aig.extends_trans hgg1 hgg2
                refine fac_oom_exit (k := 5) (by decide) ((hfr1.trans hfr2).trans hfr3)
                  (Ref.Aig.extends_trans hgg12 hgg3) (by omega) hinv3 hc
                  (fun _ hcap hmaxg => ?_) hm3 hQ
                apply hok3 h02
                · rw [← hgg12.1, (hfr1.trans hfr2).aig_cap]; omega
                · omega
              · have h03 : hdr3.oom = 0#32 := by bv_omega
                clear hc
                obtain ⟨hc1_lt, hc1_ev⟩ := hpost3 h03
                have hlen3 := aigInv_aigLen_mono hinv2 hinv3 hgg3
                c0_hcall hAigOr
                · refine ⟨hdr3, g3, aig3, ht3, R, hinv3,
                    fun _ => ⟨Nat.lt_of_lt_of_le hc2_lt hlen3, hc1_lt⟩, hm3, ?_⟩
                  intro res hdr4 g4 aig4 ht4 m4 hfr4 hgg4 hsz4 hinv4 _ hok4 hpost4 hm4
                  dsimp only [Arg.val]
                  c0_hstraight
                  c0_hsplit
                  · c0_hstraight
                    have hgg123 := Ref.Aig.extends_trans (Ref.Aig.extends_trans hgg1 hgg2) hgg3
                    refine fac_oom_exit (k := 6) (by decide)
                      (((hfr1.trans hfr2).trans hfr3).trans hfr4)
                      (Ref.Aig.extends_trans hgg123 hgg4) (by omega) hinv4 hc
                      (fun _ hcap hmaxg => ?_) hm4 hQ
                    apply hok4 h03
                    · rw [← hgg123.1, ((hfr1.trans hfr2).trans hfr3).aig_cap]; omega
                    · omega
                  · have h04 : hdr4.oom = 0#32 := by bv_omega
                    clear hc
                    c0_hstraight
                    obtain ⟨hres_lt, hres_ev⟩ := hpost4 h04
                    have hgg12 := Ref.Aig.extends_trans hgg1 hgg2
                    have hgg13 := Ref.Aig.extends_trans hgg12 hgg3
                    have hfr04 := ((hfr1.trans hfr2).trans hfr3).trans hfr4
                    have hgg04 := Ref.Aig.extends_trans hgg13 hgg4
                    refine hQ res hdr4 g4 aig4 ht4 m4 hfr04 hgg04 (by omega) hinv4
                      (fun hne => absurd h0 hne) (fun _ _ _ => h04) ?_
                      (fun hne => absurd h04 hne) hm4
                    refine fun _ => ⟨h0, hres_lt, fun ρ => ?_⟩
                    have hc2_eq : g3.evalLit ρ (UInt32.ofBitVec c2) =
                        (((g.evalLit ρ (UInt32.ofBitVec a)) ^^
                          (g.evalLit ρ (UInt32.ofBitVec b))) &&
                        g.evalLit ρ (UInt32.ofBitVec cin)) := by
                      rw [evalLit_extend_of_lt hinv2 hgg3 hc2_lt ρ, hc2_ev ρ, hp1_ev ρ,
                        evalLit_extend_of_lt hinv0 hgg1 hc0 ρ]
                    have hc1_eq : g3.evalLit ρ (UInt32.ofBitVec c1) =
                        ((g.evalLit ρ (UInt32.ofBitVec a)) &&
                        (g.evalLit ρ (UInt32.ofBitVec b))) := by
                      rw [hc1_ev ρ,
                        evalLit_extend_of_lt hinv0 hgg12 ha0 ρ,
                        evalLit_extend_of_lt hinv0 hgg12 hb0 ρ]
                    rw [hres_ev ρ, hc2_eq, hc1_eq]
                    dsimp only
                    rw [bool_atLeastTwo_eq_adder]

end

end LeanQbe.T.Examples.Bitblast.Proof
