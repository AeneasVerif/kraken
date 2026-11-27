/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Bitblast.Proof.Specs
public import LeanQbe.T.Examples.Bitblast.Src.Aig
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.MemLemmas

/-!
# Flat-Array AIG & `lits` Pool WP Proofs (`Bitblast.Proof.Aig`)

Proves all `11` canonical `Γ`-parametric `Func.wp` theorems for `Bitblast.Src.Aig`:
`bv_hash_pair_wp`, `bv_aig_init_wp`, `bv_mk_and_wp`, `bv_aig_not_wp`, `bv_aig_or_wp`,
`bv_aig_xor_wp`, `bv_aig_beq_wp`, `bv_aig_ite_wp`, `bv_lits_mark_wp`,
`bv_lits_release_wp`, and `bv_lits_alloc_wp`.

Notice `bv_mk_and_wp` requires **zero** `Cache.WF` invariant on `htSlots`: it relies solely on
the dynamic verification `A < idx && idx < len && aig[idx] == key`, `packAigGate_inj`, and
`Aig.pushNode_{wf,extends,evalLit}`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Bitblast.Proof

open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofKit
open LeanQbe.T.ProofUtil
open Std.ExtHashMap
open LeanQbe.T.Examples.Bitblast.Src
open LeanQbe.T.Examples.Bitblast.Src.Aig
open LeanQbe.T.Examples.Bitblast.Ref

/-! ## 1. Local `BVHdr` & `array64` Memory Accessors (`@[local c0_load]` / `@[local c0_store]`) -/

@[local c0_load] private theorem c0_load_hdr_aig_ptr {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i64 (h + 24) = some s.aig_ptr :=
  load_hdr_aig_ptr hm

@[local c0_load] private theorem c0_load_hdr_ht_ptr {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i64 (h + 32) = some s.ht_ptr :=
  load_hdr_ht_ptr hm

@[local c0_load] private theorem c0_load_hdr_num_atoms {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i32 (h + 96) = some s.num_atoms :=
  load_hdr_num_atoms hm

@[local c0_load] private theorem c0_load_hdr_aig_len {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i32 (h + 100) = some s.aig_len :=
  load_hdr_aig_len hm

@[local c0_load] private theorem c0_load_hdr_aig_cap {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i32 (h + 104) = some s.aig_cap :=
  load_hdr_aig_cap hm

@[local c0_load] private theorem c0_load_hdr_ht_mask {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i32 (h + 108) = some s.ht_mask :=
  load_hdr_ht_mask hm

@[local c0_load] private theorem c0_load_hdr_lits_len {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i32 (h + 112) = some s.lits_len :=
  load_hdr_lits_len hm

@[local c0_load] private theorem c0_load_hdr_lits_cap {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i32 (h + 116) = some s.lits_cap :=
  load_hdr_lits_cap hm

@[local c0_load] private theorem c0_load_hdr_oom {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i32 (h + 120) = some s.oom :=
  load_hdr_oom hm

@[local c0_store] private theorem c0_store_hdr_aig_ptr {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 64) (hm : (bvHdrMem h s ⋆ R) m) :
    storeOk m i64 (h + 24) ∧
      (bvHdrMem h { s with aig_ptr := v } ⋆ R) (storeMem m i64 (h + 24) v) :=
  store_hdr_aig_ptr v hm

@[local c0_store] private theorem c0_store_hdr_ht_ptr {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 64) (hm : (bvHdrMem h s ⋆ R) m) :
    storeOk m i64 (h + 32) ∧
      (bvHdrMem h { s with ht_ptr := v } ⋆ R) (storeMem m i64 (h + 32) v) :=
  store_hdr_ht_ptr v hm

@[local c0_store] private theorem c0_store_hdr_num_atoms {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hm : (bvHdrMem h s ⋆ R) m) :
    storeOk m i32 (h + 96) ∧
      (bvHdrMem h { s with num_atoms := v } ⋆ R) (storeMem m i32 (h + 96) v) :=
  store_hdr_num_atoms v hm

@[local c0_store] private theorem c0_store_hdr_aig_len {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hm : (bvHdrMem h s ⋆ R) m) :
    storeOk m i32 (h + 100) ∧
      (bvHdrMem h { s with aig_len := v } ⋆ R) (storeMem m i32 (h + 100) v) :=
  store_hdr_aig_len v hm

@[local c0_store] private theorem c0_store_hdr_aig_cap {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hm : (bvHdrMem h s ⋆ R) m) :
    storeOk m i32 (h + 104) ∧
      (bvHdrMem h { s with aig_cap := v } ⋆ R) (storeMem m i32 (h + 104) v) :=
  store_hdr_aig_cap v hm

@[local c0_store] private theorem c0_store_hdr_ht_mask {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hm : (bvHdrMem h s ⋆ R) m) :
    storeOk m i32 (h + 108) ∧
      (bvHdrMem h { s with ht_mask := v } ⋆ R) (storeMem m i32 (h + 108) v) :=
  store_hdr_ht_mask v hm

@[local c0_store] private theorem c0_store_hdr_lits_len {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hm : (bvHdrMem h s ⋆ R) m) :
    storeOk m i32 (h + 112) ∧
      (bvHdrMem h { s with lits_len := v } ⋆ R) (storeMem m i32 (h + 112) v) :=
  store_hdr_lits_len v hm

@[local c0_store] private theorem c0_store_hdr_oom {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hm : (bvHdrMem h s ⋆ R) m) :
    storeOk m i32 (h + 120) ∧
      (bvHdrMem h { s with oom := v } ⋆ R) (storeMem m i32 (h + 120) v) :=
  store_hdr_oom v hm

@[local c0_load] private theorem c0_load_array64_u32_mem {a : BitVec 64} {i : BitVec 32}
    {xs : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array64 a xs ⋆ R) m) (hi : i.toNat < xs.length) :
    loadVal m i64 (a + i.setWidth 64 * 8) = some (xs[i.toNat]'hi) := by
  rw [array64_eq_array] at hm
  exact c0_load_array_i64_u32 hm hi

@[local c0_store] private theorem c0_store_array64_u32_mem {a : BitVec 64} {i : BitVec 32}
    {xs : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64}
    (v : BitVec 64) (hm : (array64 a xs ⋆ R) m) (hi : i.toNat < xs.length) :
    storeOk m i64 (a + i.setWidth 64 * 8) ∧
      (array64 a (xs.set i.toNat v) ⋆ R) (storeMem m i64 (a + i.setWidth 64 * 8) v) := by
  rw [array64_eq_array] at hm ⊢
  exact c0_store_array_i64_u32 v hm hi

/-! ## 2. Pure `Aig`, `BitVec`, & `AigInv` Helpers -/

private theorem u32_ofBv_xor1 (l : BitVec 32) :
    UInt32.ofBitVec (l ^^^ 1#32) = UInt32.ofBitVec l ^^^ 1 := by
  apply UInt32.toBitVec_inj.mp
  rfl

private theorem evalLit_ofBv_xor1 (g : Aig) (ρ : Nat → Bool) (l : BitVec 32) :
    g.evalLit ρ (UInt32.ofBitVec (l ^^^ 1#32)) = !(g.evalLit ρ (UInt32.ofBitVec l)) := by
  rw [u32_ofBv_xor1, Aig.evalLit_xor_one]

private theorem bv32_xor1_shr1_toNat (l : BitVec 32) :
    ((l ^^^ 1#32) >>> 1).toNat = (l >>> 1).toNat :=
  bv_c0_toNat_xor_one_ushiftRight_32 l

private theorem u32_ofBv_shr1_toNat (l : BitVec 32) :
    ((UInt32.ofBitVec l) >>> 1).toNat = (l >>> 1).toNat := by
  rw [UInt32.toNat_shiftRight, show (1 : UInt32).toNat = 1 from rfl,
    show 1 % 32 = 1 from rfl, Nat.shiftRight_eq_div_pow, Nat.pow_one,
    bv_c0_toNat_ushiftRight_nat, Nat.pow_one]
  rfl

private theorem packAigGate_zext_shl32 (l r : BitVec 32) :
    l.setWidth 64 ||| (r.setWidth 64 <<< 32) =
      packAigGate (UInt32.ofBitVec l) (UInt32.ofBitVec r) := rfl

private theorem bv32_shl1_shr1_toNat {x : BitVec 32} (hx : x.toNat < 2 ^ 31) :
    ((x <<< 1) >>> 1).toNat = x.toNat := by
  rw [bv_c0_toNat_ushiftRight_nat, bv_c0_toNat_shiftLeft_nat, Nat.pow_one,
    Nat.mod_eq_of_lt (by omega)]
  omega

private theorem u32_ofBv_shl1 {x : BitVec 32} (hx : x.toNat < 2 ^ 31) :
    UInt32.ofBitVec (x <<< 1) = UInt32.ofNat (2 * x.toNat) := by
  apply UInt32.toBitVec_inj.mp
  apply BitVec.eq_of_toNat_eq
  change (x <<< 1).toNat = (UInt32.ofNat (2 * x.toNat)).toNat
  rw [UInt32.toNat_ofNat', bv_c0_toNat_shiftLeft_nat, Nat.pow_one,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

private theorem evalLit_two_mul_node (g : Aig) (ρ : Nat → Bool) {idx : BitVec 32}
    (hidx : idx.toNat < 2 ^ 31) :
    g.evalLit ρ (UInt32.ofBitVec (idx <<< 1)) = g.evalNode ρ idx.toNat := by
  unfold Aig.evalLit
  have hlsr : ((UInt32.ofBitVec (idx <<< 1)) >>> 1).toNat = idx.toNat := by
    rw [u32_ofBv_shr1_toNat, bv32_shl1_shr1_toNat hidx]
  have hand : (UInt32.ofBitVec (idx <<< 1) &&& 1) = 0 := by
    apply UInt32.toBitVec_inj.mp
    apply BitVec.eq_of_toNat_eq
    change ((idx <<< 1) &&& 1#32).toNat = 0
    rw [bv_c0_toNat_and_one_32, bv_c0_toNat_shiftLeft_nat, Nat.pow_one,
      Nat.mod_eq_of_lt (show idx.toNat * 2 < 2 ^ 32 by omega)]
    omega
  rw [hlsr, hand]
  simp

private theorem evalLit_hit_gate {g : Aig} (hwf : g.Wf) (ρ : Nat → Bool) {idx l r : BitVec 32}
    {i : Nat} (hi : i < g.nodes.size) (hidx : idx.toNat = g.A + 1 + i)
    (hbd : idx.toNat < 2 ^ 31)
    (hl : g.nodes[i].1 = UInt32.ofBitVec l) (hr : g.nodes[i].2 = UInt32.ofBitVec r) :
    g.evalLit ρ (UInt32.ofBitVec (idx <<< 1)) =
      (g.evalLit ρ (UInt32.ofBitVec l) && g.evalLit ρ (UInt32.ofBitVec r)) := by
  rw [evalLit_two_mul_node g ρ hbd, hidx, Aig.evalNode_gate hwf ρ hi, hl, hr]

private theorem aigInv_pushNode {hdr : BVHdrState} {g : Aig} {aigWords : List (BitVec 64)}
    {htSlots : List (BitVec 32)} (hinv : AigInv hdr g aigWords htSlots)
    {l r : BitVec 32} (wslot : BitVec 32)
    (hl : (l >>> 1).toNat < hdr.aig_len.toNat) (hr : (r >>> 1).toNat < hdr.aig_len.toNat)
    (hcap : hdr.aig_len.toNat < hdr.aig_cap.toNat)
    (hmax : g.nodes.size < bvMaxGates) :
    let len := hdr.aig_len
    let key := packAigGate (UInt32.ofBitVec l) (UInt32.ofBitVec r)
    let res := g.pushNode (UInt32.ofBitVec l) (UInt32.ofBitVec r)
    AigInv { hdr with aig_len := len + 1#32 } res.1 (aigWords.set len.toNat key)
      (htSlots.set wslot.toNat len) := by
  intro len key res
  have hlen_eq : len.toNat = g.A + 1 + g.nodes.size := hinv.aig_len_eq
  have hcap_lt : aigWords.length < bvDimacsBound := hinv.aig_cap_lt
  have hl' : ((UInt32.ofBitVec l) >>> 1).toNat < g.A + 1 + g.nodes.size := by
    rw [u32_ofBv_shr1_toNat, ← hlen_eq]; exact hl
  have hr' : ((UInt32.ofBitVec r) >>> 1).toNat < g.A + 1 + g.nodes.size := by
    rw [u32_ofBv_shr1_toNat, ← hlen_eq]; exact hr
  have hlen_lt_cap : len.toNat < aigWords.length := hinv.aig_cap_eq ▸ hcap
  have hdim : bvDimacsBound = 268435456 := rfl
  have hlen_plus1_lt32 : len.toNat + 1 < 2 ^ 32 := by omega
  refine ⟨Aig.pushNode_wf hinv.wf hl' hr', hinv.num_atoms_eq, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · simp [res, Aig.pushNode, hlen_eq, BitVec.toNat_add]
    omega
  · simp [res, Aig.pushNode, List.length_set]
    omega
  · simpa [List.length_set] using hinv.aig_cap_eq
  · simpa [List.length_set] using hinv.aig_cap_lt
  · simp [res, Aig.pushNode]
    omega
  · refine ⟨by simp [res, Aig.pushNode, List.length_set]; omega, fun i hi => ?_⟩
    simp only [res, Aig.pushNode, Array.size_push] at hi
    simp only [res, Aig.pushNode, Array.getElem_push]
    by_cases hlt : i < g.nodes.size
    · have hne : len.toNat ≠ g.A + 1 + i := by omega
      simp only [hlt, ↓reduceDIte]
      rw [List.getElem_set_ne hne]
      exact hinv.words_match.gate_eq i hlt
    · have heq : i = g.nodes.size := by omega
      subst heq
      simp only [Nat.lt_irrefl, ↓reduceDIte, ← hlen_eq]
      rw [List.getElem_set_self (by simpa [List.length_set] using hlen_lt_cap)]
  · simpa [List.length_set] using hinv.ht_len
  · simpa [List.length_set] using hinv.ht_mask_lt
  · simpa [List.length_set] using hinv.ht_pos
  · simpa [List.length_set] using hinv.ht_bound

private theorem bv_lits_release_hdr_eq (hdr : BVHdrState) :
    { hdr with lits_len := hdr.lits_len } = hdr := by
  cases hdr; rfl

private theorem list_eq_replicate_of_getD {xs : List (BitVec 32)} {n : Nat}
    (hlen : xs.length = n) (hz : ∀ k < n, xs.getD k 1#32 = 0#32) :
    xs = List.replicate n 0#32 := by
  apply List.ext_getElem
  · simpa using hlen
  · intro i hi1 hi2
    have hi_n : i < n := hlen ▸ hi1
    have hget := hz i hi_n
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi1, Option.getD_some] at hget
    simpa [List.getElem_replicate] using hget

private theorem aigBin_eval_or (a b : Bool) : (!((!a) && (!b))) = (a || b) := by
  cases a <;> cases b <;> rfl

private theorem aigBin_eval_xor (a b : Bool) : (!(a && b) && !(!a && !b)) = (a ^^ b) := by
  cases a <;> cases b <;> rfl

private theorem aigBin_eval_beq (a b : Bool) : (!(a ^^ b)) = (a == b) := by
  cases a <;> cases b <;> rfl

private theorem aigBin_eval_ite (c t f : Bool) :
    (!(!(c && t) && !(!c && f))) = cond c t f := by
  cases c <;> cases t <;> cases f <;> rfl

private theorem aig_ite_t {P : Prop} [Decidable P] {α : Type _} {a b : α} (h : P) :
    (if P then a else b) = a := by
  split
  · rfl
  · contradiction

private theorem aig_ite_f {P : Prop} [Decidable P] {α : Type _} {a b : α} (h : ¬ P) :
    (if P then a else b) = b := by
  split
  · contradiction
  · rfl

/-! ## 3. Multi-Call Helper for `bv_mk_and` Composition -/

private theorem bv_mk_and_step {Γ : Env}
    (hMkAnd : ∀ xs m Q X, bvMkAndSpec xs m Q X →
      Γ "bv_mk_and" [i64, i32, i32] [i32] xs m Q X)
    {rs : List Ty} {Q : Post rs} {X : XPost}
    {h : Val i64} (lhs rhs : Val i32) {hdr : BVHdrState} {g : Aig}
    {aigWords : List (BitVec 64)} {htSlots : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64}
    {k : Tup Val [i32] → Expr Val Cont rs}
    (hinv : AigInv hdr g aigWords htSlots)
    (hbd : hdr.oom = 0#32 →
      (lhs >>> 1).toNat < hdr.aig_len.toNat ∧ (rhs >>> 1).toNat < hdr.aig_len.toNat)
    (hm : (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aigWords ⋆
      array (t := i32) hdr.ht_ptr htSlots ⋆ R) m)
    (hk : ∀ (ret : BitVec 32) (hdr' : BVHdrState) (g' : Aig)
      (aigWords' : List (BitVec 64)) (htSlots' : List (BitVec 32)) (m' : Mem 64),
      hdr.AigFrame hdr' →
      g ≤ g' →
      g'.nodes.size ≤ g.nodes.size + 1 →
      AigInv hdr' g' aigWords' htSlots' →
      (hdr.oom ≠ 0#32 → hdr'.oom ≠ 0#32) →
      (hdr.oom = 0#32 → g.A + 1 + g.nodes.size + 1 ≤ hdr.aig_cap.toNat →
        g.nodes.size + 1 ≤ bvMaxGates → hdr'.oom = 0#32) →
      (hdr'.oom = 0#32 →
        (ret >>> 1).toNat < hdr'.aig_len.toNat ∧
        ∀ ρ : Nat → Bool,
          g'.evalLit ρ (UInt32.ofBitVec ret) =
            (g.evalLit ρ (UInt32.ofBitVec lhs) && g.evalLit ρ (UInt32.ofBitVec rhs))) →
      (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aigWords' ⋆
        array (t := i32) hdr'.ht_ptr htSlots' ⋆ R) m' →
      wp Γ Q X (k (ret, ())) m') :
    wp Γ Q X (.call "bv_mk_and" (as := [i64, i32, i32]) (bs := [i32])
      (Arg.var (t := i64) h, Arg.var (t := i32) lhs, Arg.var (t := i32) rhs, ()) k) m := by
  c0_call hMkAnd
  exact ⟨hdr, g, aigWords, htSlots, R, hinv, hbd, hm,
    fun ret hdr' g' aw' ht' m' hfr hext hsz hinv' hoom1 hoom0 heval hm' =>
      hk ret hdr' g' aw' ht' m' hfr hext hsz hinv' hoom1 hoom0 heval hm'⟩

/-! ## 4. Canonical `Γ`-Parametric WP Theorems (`11` Functions) -/

public section

theorem bv_hash_pair_wp (Γ : Env) :
    ∀ xs m Q X, bvHashPairSpec xs m Q X → Func.wp Γ bv_hash_pair_body xs m Q X := by
  rintro ⟨lhs, rhs, ⟨⟩⟩ m Q X hQ
  c0_hsteps
  exact hQ _

theorem bv_aig_init_wp (Γ : Env) :
    ∀ xs m Q X, bvAigInitSpec xs m Q X → Func.wp Γ bv_aig_init_body xs m Q X := by
  rintro ⟨h, aigPtr, aigCap, htPtr, htMask, numAtoms, ⟨⟩⟩ m Q X
    ⟨hdr, htSlots, R, hlen, hbd, hna, hm, hQ⟩
  c0_hsteps_nogrp
  let hdr' : BVHdrState :=
    { hdr with
      aig_ptr := aigPtr, aig_cap := aigCap, ht_ptr := htPtr,
      ht_mask := htMask, num_atoms := numAtoms,
      aig_len := numAtoms + 1#32, oom := 0#32 }
  have hna_eq : numAtoms + 1#32 = BitVec.ofNat 32 (numAtoms.toNat + 1) := by
    apply BitVec.eq_of_toNat_eq; c0_bv_omega [hna]
  have hnslots : (htMask.setWidth 64 + 1).toNat = htSlots.length := by
    c0_bv_omega [hlen, hbd]
  refine wp_while_state (ts := [i64]) (α := Nat × List (BitVec 32))
    (fun st => (BitVec.ofNat 64 st.1, ()))
    (fun st => htSlots.length - st.1)
    (fun st ml =>
      st.1 ≤ htSlots.length ∧
      st.2.length = htSlots.length ∧
      (∀ k < st.1, st.2.getD k 1#32 = 0#32) ∧
      (bvHdrMem h hdr' ⋆ array (t := i32) htPtr st.2 ⋆ R) ml)
    ?_ ?_
  · intro J hJ
    c0_hsteps
    refine hJ (0, htSlots) m ⟨Nat.zero_le _, rfl, fun _ hk => by omega, ?_⟩
    simp only [sep_emp] at hm
    simpa [hdr'] using sep_ac hm
  · intro J st ml ⟨hidx_le, hcur_len, hzero, hml⟩ ih
    c0_hstraight
    c0_hsplit
    · have hidx_lt : st.1 < st.2.length := by
        have hlt_bv : (BitVec.ofNat 64 st.1).toNat < (htMask.setWidth 64 + 1).toNat := by
          simpa [BitVec.ult] using hc
        rw [hnslots] at hlt_bv
        c0_bv_omega [hidx_le, hbd, hlen, hlt_bv, hcur_len]
      clear hc
      c0_hsteps
      have hidx_lt_len : st.1 < htSlots.length := by omega
      have hidx64 : BitVec.ofNat 64 st.1 + 1 = BitVec.ofNat 64 (st.1 + 1) := by
        apply BitVec.eq_of_toNat_eq; c0_bv_omega [hidx_lt_len, hbd]
      have hidx32 : (BitVec.ofNat 64 st.1).toNat = st.1 := by
        c0_bv_omega [hidx_lt_len, hbd]
      rw [hidx64]
      refine ih (st.1 + 1, st.2.set st.1 0#32) m (by omega)
        ⟨hidx_lt_len, by simpa using hcur_len, fun k hk => ?_, ?_⟩
      · by_cases hki : k = st.1
        · subst hki
          simp [List.getD_eq_getElem?_getD, hidx_lt]
        · rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (by omega)]
          exact hzero k (by omega)
      · dsimp only
        rw [hidx32] at hm
        simp only [sep_emp] at hm
        change (array (t := i32) htPtr (st.2.set st.1 0#32) ⋆ (bvHdrMem h hdr' ⋆ R)) m at hm
        exact sep_ac hm
    · have hidx_eq : st.1 = htSlots.length := by
        have hge : ¬ (BitVec.ofNat 64 st.1).toNat < (htMask.setWidth 64 + 1).toNat := by
          simpa [BitVec.ult] using hc
        rw [hnslots] at hge
        c0_bv_omega [hidx_le, hbd, hlen, hge]
      clear hc
      c0_hsteps
      have hrep := list_eq_replicate_of_getD hcur_len (by simpa [hidx_eq] using hzero)
      rw [hrep, hlen] at hml
      exact hQ ml hml

private theorem bv_mk_and_push_post {Q : Post [i32]} {h : Val i64} {lhs rhs l r wslot : BitVec 32}
    {hdr : BVHdrState} {g : Aig} {aigWords : List (BitVec 64)} {htSlots : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hinv : AigInv hdr g aigWords htSlots)
    (hl_lt : (l >>> 1).toNat < hdr.aig_len.toNat)
    (hr_lt : (r >>> 1).toNat < hdr.aig_len.toNat)
    (heval_lr : ∀ ρ : Nat → Bool,
      (g.evalLit ρ (UInt32.ofBitVec l) && g.evalLit ρ (UInt32.ofBitVec r)) =
        (g.evalLit ρ (UInt32.ofBitVec lhs) && g.evalLit ρ (UInt32.ofBitVec rhs)))
    (hoom0 : hdr.oom = 0#32) (hcap_ok : hdr.aig_len.toNat < hdr.aig_cap.toNat)
    (hlen_dim : hdr.aig_len.toNat < bvDimacsBound) (hng_max : g.nodes.size < bvMaxGates)
    (hm : (bvHdrMem h { hdr with aig_len := hdr.aig_len + 1#32 } ⋆
      array64 hdr.aig_ptr (aigWords.set hdr.aig_len.toNat
        (packAigGate (UInt32.ofBitVec l) (UInt32.ofBitVec r))) ⋆
      array (t := i32) hdr.ht_ptr (htSlots.set wslot.toNat hdr.aig_len) ⋆ R) m)
    (hQ : ∀ (ret : BitVec 32) (hdr' : BVHdrState) (g' : Aig)
      (aigWords' : List (BitVec 64)) (htSlots' : List (BitVec 32)) (m' : Mem 64),
      hdr.AigFrame hdr' → g ≤ g' → g'.nodes.size ≤ g.nodes.size + 1 →
      AigInv hdr' g' aigWords' htSlots' → (hdr.oom ≠ 0#32 → hdr'.oom ≠ 0#32) →
      (hdr.oom = 0#32 → g.A + 1 + g.nodes.size + 1 ≤ hdr.aig_cap.toNat →
        g.nodes.size + 1 ≤ bvMaxGates → hdr'.oom = 0#32) →
      (hdr'.oom = 0#32 → (ret >>> 1).toNat < hdr'.aig_len.toNat ∧ ∀ ρ : Nat → Bool,
        g'.evalLit ρ (UInt32.ofBitVec ret) =
          (g.evalLit ρ (UInt32.ofBitVec lhs) && g.evalLit ρ (UInt32.ofBitVec rhs))) →
      (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aigWords' ⋆
        array (t := i32) hdr'.ht_ptr htSlots' ⋆ R) m' →
      Q (ret, ()) m') :
    Q (hdr.aig_len <<< 1, ()) m := by
  have hdim_val : bvDimacsBound = 268435456 := rfl
  have hlen_plus1_lt32 : hdr.aig_len.toNat + 1 < 2 ^ 32 := by
    rw [hdim_val] at hlen_dim; omega
  have hlen_lt_31 : hdr.aig_len.toNat < 2 ^ 31 := by
    rw [hdim_val] at hlen_dim; omega
  let key := packAigGate (UInt32.ofBitVec l) (UInt32.ofBitVec r)
  let res := g.pushNode (UInt32.ofBitVec l) (UInt32.ofBitVec r)
  have hinv' := aigInv_pushNode hinv wslot hl_lt hr_lt hcap_ok hng_max
  refine hQ (hdr.aig_len <<< 1) { hdr with aig_len := hdr.aig_len + 1#32 } res.1
    (aigWords.set hdr.aig_len.toNat key) (htSlots.set wslot.toNat hdr.aig_len) m
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl⟩
    (Aig.pushNode_extends g (UInt32.ofBitVec l) (UInt32.ofBitVec r))
    (by simp [res, Aig.pushNode]) hinv' (fun h => absurd hoom0 h)
    (fun _ _ _ => hoom0) (fun _ => ⟨?_, fun ρ => ?_⟩) ?_
  · have : (hdr.aig_len <<< 1 >>> 1).toNat = hdr.aig_len.toNat :=
      bv32_shl1_shr1_toNat hlen_lt_31
    c0_bv_omega [this, hlen_plus1_lt32]
  · have hres_eq : UInt32.ofBitVec (hdr.aig_len <<< 1) = res.2 := by
      rw [u32_ofBv_shl1 hlen_lt_31, hinv.aig_len_eq]
      rfl
    have hbound : 2 * (g.A + 1 + g.nodes.size) < 4294967296 := by
      rw [← hinv.aig_len_eq]; omega
    have hl' : ((UInt32.ofBitVec l) >>> 1).toNat < g.A + 1 + g.nodes.size := by
      rw [u32_ofBv_shr1_toNat, ← hinv.aig_len_eq]; exact hl_lt
    have hr' : ((UInt32.ofBitVec r) >>> 1).toNat < g.A + 1 + g.nodes.size := by
      rw [u32_ofBv_shr1_toNat, ← hinv.aig_len_eq]; exact hr_lt
    rw [hres_eq, Aig.pushNode_evalLit hinv.wf ρ hl' hr' hbound, heval_lr]
  · dsimp only
    exact hm

private theorem bv_mk_and_oom_post {Q : Post [i32]} {h : Val i64} {lhs rhs : BitVec 32}
    {hdr : BVHdrState} {g : Aig} {aigWords : List (BitVec 64)} {htSlots : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hinv : AigInv hdr g aigWords htSlots) (hoom0 : hdr.oom = 0#32)
    (hfail : ¬(hdr.aig_len.toNat < hdr.aig_cap.toNat ∧ g.nodes.size < bvMaxGates))
    (hm : (bvHdrMem h { hdr with oom := 1#32 } ⋆
      (array64 hdr.aig_ptr aigWords ⋆ (array (t := i32) hdr.ht_ptr htSlots ⋆ R))) m)
    (hQ : ∀ (ret : BitVec 32) (hdr' : BVHdrState) (g' : Aig)
      (aigWords' : List (BitVec 64)) (htSlots' : List (BitVec 32)) (m' : Mem 64),
      hdr.AigFrame hdr' → g ≤ g' → g'.nodes.size ≤ g.nodes.size + 1 →
      AigInv hdr' g' aigWords' htSlots' → (hdr.oom ≠ 0#32 → hdr'.oom ≠ 0#32) →
      (hdr.oom = 0#32 → g.A + 1 + g.nodes.size + 1 ≤ hdr.aig_cap.toNat →
        g.nodes.size + 1 ≤ bvMaxGates → hdr'.oom = 0#32) →
      (hdr'.oom = 0#32 → (ret >>> 1).toNat < hdr'.aig_len.toNat ∧ ∀ ρ : Nat → Bool,
        g'.evalLit ρ (UInt32.ofBitVec ret) =
          (g.evalLit ρ (UInt32.ofBitVec lhs) && g.evalLit ρ (UInt32.ofBitVec rhs))) →
      (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aigWords' ⋆
        array (t := i32) hdr'.ht_ptr htSlots' ⋆ R) m' →
      Q (ret, ()) m') :
    Q (0#32, ()) m := by
  refine hQ 0#32 { hdr with oom := 1#32 } g aigWords htSlots m
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl⟩
    (Aig.extends_rfl g) (Nat.le_succ _) { hinv with } (fun h => absurd hoom0 h) ?_
    (fun h => by cases h) ?_
  · intro _ hcap_ok hmax_ok
    exfalso; apply hfail
    have := hinv.aig_len_eq
    exact ⟨by omega, by omega⟩
  · dsimp only
    exact sep_ac hm

private theorem bv_mk_and_hit_post {Q : Post [i32]} {h : Val i64} {lhs rhs l r idx : BitVec 32}
    {hdr : BVHdrState} {g : Aig} {aigWords : List (BitVec 64)} {htSlots : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hinv : AigInv hdr g aigWords htSlots)
    (heval_lr : ∀ ρ : Nat → Bool,
      (g.evalLit ρ (UInt32.ofBitVec l) && g.evalLit ρ (UInt32.ofBitVec r)) =
        (g.evalLit ρ (UInt32.ofBitVec lhs) && g.evalLit ρ (UInt32.ofBitVec rhs)))
    (hoom0 : hdr.oom = 0#32)
    (hidx_gt : hdr.num_atoms.toNat < idx.toNat) (hidx_lt : idx.toNat < hdr.aig_len.toNat)
    (hidx_lt_aw : idx.toNat < aigWords.length)
    (hkey_eq : aigWords[idx.toNat]'hidx_lt_aw =
      packAigGate (UInt32.ofBitVec l) (UInt32.ofBitVec r))
    (hm : (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aigWords ⋆
      array (t := i32) hdr.ht_ptr htSlots ⋆ R) m)
    (hQ : ∀ (ret : BitVec 32) (hdr' : BVHdrState) (g' : Aig)
      (aigWords' : List (BitVec 64)) (htSlots' : List (BitVec 32)) (m' : Mem 64),
      hdr.AigFrame hdr' → g ≤ g' → g'.nodes.size ≤ g.nodes.size + 1 →
      AigInv hdr' g' aigWords' htSlots' → (hdr.oom ≠ 0#32 → hdr'.oom ≠ 0#32) →
      (hdr.oom = 0#32 → g.A + 1 + g.nodes.size + 1 ≤ hdr.aig_cap.toNat →
        g.nodes.size + 1 ≤ bvMaxGates → hdr'.oom = 0#32) →
      (hdr'.oom = 0#32 → (ret >>> 1).toNat < hdr'.aig_len.toNat ∧ ∀ ρ : Nat → Bool,
        g'.evalLit ρ (UInt32.ofBitVec ret) =
          (g.evalLit ρ (UInt32.ofBitVec lhs) && g.evalLit ρ (UInt32.ofBitVec rhs))) →
      (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aigWords' ⋆
        array (t := i32) hdr'.ht_ptr htSlots' ⋆ R) m' →
      Q (ret, ()) m') :
    Q (idx <<< 1, ()) m := by
  have hi_lt : idx.toNat - (g.A + 1) < g.nodes.size := by
    have := hinv.num_atoms_eq; have := hinv.aig_len_eq; omega
  have hidx_eq : idx.toNat = g.A + 1 + (idx.toNat - (g.A + 1)) := by
    have := hinv.num_atoms_eq; omega
  have hgate := hinv.words_match.gate_eq _ hi_lt
  simp only [← hidx_eq] at hgate
  rw [hgate] at hkey_eq
  have ⟨hl_eq, hr_eq⟩ := packAigGate_inj hkey_eq
  have hidx_31 : idx.toNat < 2 ^ 31 := by
    have := hinv.aig_cap_lt; unfold bvDimacsBound at this; omega
  refine hQ (idx <<< 1) hdr g aigWords htSlots m
    (BVHdrState.AigFrame.rfl hdr) (Aig.extends_rfl g) (Nat.le_succ _) hinv
    (fun h => absurd hoom0 h) (fun _ _ _ => hoom0) (fun _ => ⟨?_, fun ρ => ?_⟩) hm
  · have hshr := bv32_shl1_shr1_toNat hidx_31
    c0_bv_omega [hshr, hidx_lt]
  · rw [evalLit_hit_gate hinv.wf ρ hi_lt hidx_eq hidx_31 hl_eq hr_eq, heval_lr]

theorem bv_mk_and_wp (Γ : Env)
    (hHash : ∀ xs m Q X, bvHashPairSpec xs m Q X →
      Γ "bv_hash_pair" [i32, i32] [i32] xs m Q X) :
    ∀ xs m Q X, bvMkAndSpec xs m Q X → Func.wp Γ bv_mk_and_body xs m Q X := by
  rintro ⟨h, lhs, rhs, ⟨⟩⟩ m Q X
    ⟨hdr, g, aigWords, htSlots, R, hinv, hbd_in, hm, hQ⟩
  c0_hstraight; c0_hsplit
  · have hoom_ne : hdr.oom ≠ 0#32 := by c0_bv_omega [hc]
    c0_hsteps
    exact hQ 0#32 hdr g aigWords htSlots m (BVHdrState.AigFrame.rfl hdr) (Aig.extends_rfl g)
      (Nat.le_succ _) hinv (fun _ => hoom_ne)
      (fun h0 => absurd h0 hoom_ne) (fun h0 => absurd h0 hoom_ne) hm
  have hoom0 : hdr.oom = 0#32 := by c0_bv_omega [hc]
  clear hc
  have ⟨hl_bd, hr_bd⟩ := hbd_in hoom0
  have hlen_pos : 0 < hdr.aig_len.toNat := by
    have := hinv.aig_len_eq; omega
  c0_hstraight; c0_hsplit
  · have hl0 : lhs = 0#32 := by c0_bv_omega [hc]
    subst hl0; c0_hsteps
    exact hQ 0#32 hdr g aigWords htSlots m (BVHdrState.AigFrame.rfl hdr) (Aig.extends_rfl g)
      (Nat.le_succ _) hinv (fun h => absurd hoom0 h) (fun _ _ _ => hoom0)
      (fun _ => ⟨by simpa using hlen_pos, fun ρ => by simp⟩) hm
  clear hc; c0_hstraight; c0_hsplit
  · have hr0 : rhs = 0#32 := by c0_bv_omega [hc]
    subst hr0; c0_hsteps
    exact hQ 0#32 hdr g aigWords htSlots m (BVHdrState.AigFrame.rfl hdr) (Aig.extends_rfl g)
      (Nat.le_succ _) hinv (fun h => absurd hoom0 h) (fun _ _ _ => hoom0)
      (fun _ => ⟨by simpa using hlen_pos, fun ρ => by simp⟩) hm
  clear hc; c0_hstraight; c0_hsplit
  · have hl1 : lhs = 1#32 := by c0_bv_omega [hc]
    subst hl1; c0_hsteps
    exact hQ rhs hdr g aigWords htSlots m (BVHdrState.AigFrame.rfl hdr) (Aig.extends_rfl g)
      (Nat.le_succ _) hinv (fun h => absurd hoom0 h) (fun _ _ _ => hoom0)
      (fun _ => ⟨hr_bd, fun ρ => by simp⟩) hm
  clear hc; c0_hstraight; c0_hsplit
  · have hr1 : rhs = 1#32 := by c0_bv_omega [hc]
    subst hr1; c0_hsteps
    exact hQ lhs hdr g aigWords htSlots m (BVHdrState.AigFrame.rfl hdr) (Aig.extends_rfl g)
      (Nat.le_succ _) hinv (fun h => absurd hoom0 h) (fun _ _ _ => hoom0)
      (fun _ => ⟨hl_bd, fun ρ => by simp⟩) hm
  clear hc; c0_hstraight; c0_hsplit
  · have hlr : lhs = rhs := by c0_bv_omega [hc]
    subst hlr; c0_hsteps
    exact hQ lhs hdr g aigWords htSlots m (BVHdrState.AigFrame.rfl hdr) (Aig.extends_rfl g)
      (Nat.le_succ _) hinv (fun h => absurd hoom0 h) (fun _ _ _ => hoom0)
      (fun _ => ⟨hl_bd, fun ρ => by simp⟩) hm
  clear hc; c0_hstraight; c0_hsplit
  · have hcomp : lhs = rhs ^^^ 1#32 := by simpa [beq_iff_eq] using hc
    subst hcomp; c0_hsteps
    refine hQ 0#32 hdr g aigWords htSlots m (BVHdrState.AigFrame.rfl hdr) (Aig.extends_rfl g)
      (Nat.le_succ _) hinv (fun h => absurd hoom0 h) (fun _ _ _ => hoom0)
      (fun _ => ⟨by simpa using hlen_pos, fun ρ => ?_⟩) hm
    rw [evalLit_ofBv_xor1]
    simp
  clear hc
  refine wp_join_state_pure (α := BitVec 32 × BitVec 32)
    (fun lr => (lr.1, lr.2, ()))
    (fun lr => (lr.1 >>> 1).toNat < hdr.aig_len.toNat ∧
      (lr.2 >>> 1).toNat < hdr.aig_len.toNat ∧
      ∀ ρ, (g.evalLit ρ (UInt32.ofBitVec lr.1) && g.evalLit ρ (UInt32.ofBitVec lr.2)) =
        (g.evalLit ρ (UInt32.ofBitVec lhs) && g.evalLit ρ (UInt32.ofBitVec rhs)))
    ?_ ?_
  · intro J ⟨l, r⟩ ⟨hl_lt, hr_lt, heval_lr⟩
    c0_hstraight
    refine wp_join0 (fun _ => False) (fun _ _ h => h.elim) (fun J' hJ' => ?_)
    c0_hstraight
    have ha_lt_len : ¬ hdr.aig_len.toNat ≤ hdr.num_atoms.toNat := by
      have h1 := hinv.num_atoms_eq; have h2 := hinv.aig_len_eq; omega
    c0_hsplit
    · exfalso; exact ha_lt_len (by c0_bv_omega [hc])
    clear hc; c0_hstraight; c0_hsplit
    · exfalso; c0_bv_omega [hc, hl_lt]
    clear hc; c0_hstraight; c0_hsplit
    · exfalso; c0_bv_omega [hc, hr_lt]
    clear hc; clear hJ'
    c0_hstraight
    c0_call hHash
    intro h0_hash
    c0_hsteps_nogrp
    have hmask_h0 : (h0_hash &&& hdr.ht_mask).toNat < htSlots.length :=
      hinv.ht_mask_lt h0_hash
    refine wp_while_break_state
      (β := BitVec 32 × BitVec 32 × BitVec 32)
      (α := BitVec 32 × BitVec 32)
      (fun b => (b.1, b.2.1, b.2.2, ()))
      (fun b ml => ml = m ∧ b.2.1.toNat < htSlots.length)
      (fun s => (s.1, s.2, ()))
      (fun s => 16 - s.2.toNat)
      (fun s ml => ml = m ∧ s.1.toNat < htSlots.length ∧ s.2.toNat ≤ 16)
      ?_ ?_ ?_
    · intro B ⟨slot, wslot, probe⟩ m_after ⟨hm_after, hwslot⟩
      dsimp only at hwslot
      subst m_after
      c0_hstraight
      have hlen_gt : hdr.num_atoms.toNat + 1 ≤ hdr.aig_len.toNat := by
        have h1 := hinv.num_atoms_eq; have h2 := hinv.aig_len_eq; omega
      have hna1_eq : (hdr.num_atoms + 1#32).toNat = g.A + 1 := by
        have h1 := hinv.num_atoms_eq; have h2 := hinv.aig_len_eq; c0_bv_omega [h1, h2]
      have hng_eq : (hdr.aig_len - (hdr.num_atoms + 1#32)).toNat = g.nodes.size := by
        have h1 := hinv.num_atoms_eq; have h2 := hinv.aig_len_eq
        c0_bv_omega [h1, h2, hna1_eq]
      have hcap_lt_dim : hdr.aig_cap.toNat < bvDimacsBound :=
        hinv.aig_cap_eq ▸ hinv.aig_cap_lt
      have hdim_val : bvDimacsBound = 268435456 := rfl
      refine wp_join0 (fun m_oom => m_oom = m ∧
        ¬(hdr.aig_len.toNat < hdr.aig_cap.toNat ∧ g.nodes.size < bvMaxGates)) ?_ ?_
      · intro _ m_oom ⟨hm_oom, hfail⟩
        subst m_oom
        c0_hsteps
        simp only [sep_emp] at hm
        change (bvHdrMem h { hdr with oom := 1#32 } ⋆
          (array64 hdr.aig_ptr aigWords ⋆
            (array (t := i32) hdr.ht_ptr htSlots ⋆ R))) m at hm
        exact bv_mk_and_oom_post hinv hoom0 hfail hm hQ
      · intro Joom hJoom
        c0_hstraight; c0_hsplit
        · have hge : ¬ hdr.aig_len.toNat < hdr.aig_cap.toNat := by c0_bv_omega [hc]
          c0_hsteps; exact hJoom m ⟨rfl, fun ⟨h1, _⟩ => hge h1⟩
        have hcap_ok : hdr.aig_len.toNat < hdr.aig_cap.toNat := by c0_bv_omega [hc]
        clear hc; c0_hstraight; c0_hsplit
        · exfalso
          have hge : bvDimacsBound ≤ hdr.aig_len.toNat := by
            unfold bvDimacsBound; c0_bv_omega [hc]
          omega
        have hlen_dim : hdr.aig_len.toNat < bvDimacsBound := by
          unfold bvDimacsBound; c0_bv_omega [hc]
        clear hc; c0_hstraight
        have hng_bv : hdr.aig_len - (hdr.num_atoms + (1 : BitVec 32)) =
            BitVec.ofNat 32 g.nodes.size := by
          apply BitVec.eq_of_toNat_eq
          have hgs : g.nodes.size < 2 ^ 32 := by
            have := hinv.gates_bound; unfold bvMaxGates at this; omega
          rw [show (1 : BitVec 32) = 1#32 from rfl, hng_eq, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt hgs]
        refine head_wp_jnz rfl (fun hc => ?_) (fun hc => ?_)
        · have hmax_ge : bvMaxGates ≤ g.nodes.size := by
            rw [hng_bv] at hc
            have hgs : g.nodes.size < 2 ^ 32 := by
              have := hinv.gates_bound; unfold bvMaxGates at this; omega
            have hmv : (bvMaxGates : Nat) < 2 ^ 32 := by unfold bvMaxGates; decide
            rw [show (89478485 : BitVec 32) = BitVec.ofNat 32 bvMaxGates from rfl] at hc
            unfold bvMaxGates at *
            simp only [Arg.val, BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hgs,
              Nat.mod_eq_of_lt hmv, decide_eq_true_eq] at hc
            omega
          c0_hsteps
          exact hJoom m ⟨rfl, fun ⟨_, h2⟩ => by omega⟩
        have hng_max : g.nodes.size < bvMaxGates := by
          rw [hng_bv] at hc
          have hgs : g.nodes.size < 2 ^ 32 := by
            have := hinv.gates_bound; unfold bvMaxGates at this; omega
          have hmv : (bvMaxGates : Nat) < 2 ^ 32 := by unfold bvMaxGates; decide
          rw [show (89478485 : BitVec 32) = BitVec.ofNat 32 bvMaxGates from rfl] at hc
          unfold bvMaxGates at *
          simp only [Arg.val, BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hgs,
            Nat.mod_eq_of_lt hmv, decide_eq_false_iff_not] at hc
          omega
        clear hc hJoom
        have hlen_lt_aw : hdr.aig_len.toNat < aigWords.length :=
          hinv.aig_cap_eq ▸ hcap_ok
        iterate 6 c0_hstep
        have hsw : (BitVec.setWidth 64 hdr.aig_len).toNat = hdr.aig_len.toNat := by simp
        have hkey : BitVec.setWidth 64 l ||| BitVec.setWidth 64 r <<< OfNat.ofNat 32 =
            packAigGate (UInt32.ofBitVec l) (UInt32.ofBitVec r) := rfl
        rw [hsw, hkey] at hm
        iterate 7 c0_hstep
        have hwsw : (BitVec.setWidth 64 wslot).toNat = wslot.toNat := by simp
        simp only [sep_emp] at hm
        rw [hwsw] at hm
        try rw [show (1 : BitVec 32) = 1#32 from rfl] at hm
        exact bv_mk_and_push_post hinv hl_lt hr_lt heval_lr hoom0 hcap_ok hlen_dim hng_max
          (sep_ac hm) hQ
    · intro B L ⟨slot, probe⟩ ml hB hL ⟨hm_eq, hslot_lt, hprobe_le⟩
      subst ml
      c0_hstraight; c0_hsplit
      · have hprobe_lt : probe.toNat < 16 := by c0_bv_omega [hc]
        clear hc
        c0_hstraight; c0_hsplit
        · c0_hsteps
          exact hB (slot, slot, probe) m ⟨rfl, hslot_lt⟩
        clear hc
        c0_hstraight
        refine wp_join0 (fun ml' => ml' = m) ?_ ?_
        · intro _ ml' hml'
          subst ml'
          c0_hsteps
          have hslot'_lt : ((slot + 1#32) &&& hdr.ht_mask).toNat < htSlots.length :=
            hinv.ht_mask_lt (slot + 1#32)
          exact hL ((slot + 1#32) &&& hdr.ht_mask, probe + 1#32) m
            (by c0_bv_omega [hprobe_lt]) ⟨rfl, hslot'_lt, by c0_bv_omega [hprobe_lt]⟩
        · intro Jmiss hJmiss
          c0_hstraight; c0_hsplit
          · have hidx_gt : hdr.num_atoms.toNat < (htSlots[slot.toNat]).toNat := by
              c0_bv_omega [hc]
            clear hc
            c0_hstraight; c0_hsplit
            · have hidx_lt : (htSlots[slot.toNat]).toNat < hdr.aig_len.toNat := by
                c0_bv_omega [hc]
              clear hc
              have hidx_lt_aw : (htSlots[slot.toNat]).toNat < aigWords.length := by
                have := hinv.aig_len_eq; have := hinv.aig_len_le_cap; omega
              c0_hstraight; c0_hsplit
              · have hkey_eq : aigWords[(htSlots[slot.toNat]).toNat]'hidx_lt_aw =
                    packAigGate (UInt32.ofBitVec l) (UInt32.ofBitVec r) := by
                  simpa [packAigGate_zext_shl32] using hc
                clear hc
                c0_hsteps
                exact bv_mk_and_hit_post hinv heval_lr hoom0 hidx_gt hidx_lt hidx_lt_aw
                  hkey_eq hm hQ
              · c0_hsteps; exact hJmiss m rfl
            · c0_hsteps; exact hJmiss m rfl
          · c0_hsteps; exact hJmiss m rfl
      · c0_hsteps
        exact hB (slot, h0_hash &&& hdr.ht_mask, probe) m ⟨rfl, hmask_h0⟩
    · intro B L hB hL
      c0_hsteps
      exact hL (h0_hash &&& hdr.ht_mask, 0#32) m ⟨rfl, hmask_h0, by dsimp only; decide⟩
  · intro J hJ
    c0_hstraight; c0_hsplit
    · c0_hsteps
      exact hJ (rhs, lhs) ⟨hr_bd, hl_bd, fun ρ => Bool.and_comm _ _⟩
    · c0_hsteps
      exact hJ (lhs, rhs) ⟨hl_bd, hr_bd, fun _ => rfl⟩

theorem bv_aig_not_wp (Γ : Env) :
    ∀ xs m Q X, bvAigNotSpec xs m Q X → Func.wp Γ bv_aig_not_body xs m Q X := by
  rintro ⟨l, ⟨⟩⟩ m Q X hQ
  c0_hsteps
  exact hQ

theorem bv_aig_or_wp (Γ : Env)
    (hMkAnd : ∀ xs m Q X, bvMkAndSpec xs m Q X →
      Γ "bv_mk_and" [i64, i32, i32] [i32] xs m Q X) :
    ∀ xs m Q X, bvAigOrSpec xs m Q X → Func.wp Γ bv_aig_or_body xs m Q X := by
  rintro ⟨h, a, b, ⟨⟩⟩ m Q X ⟨hdr, g, aw, ht, R, hinv, hbd, hm, hQ⟩
  c0_hstraight
  dsimp only
  refine bv_mk_and_step hMkAnd (a ^^^ 1#32) (b ^^^ 1#32) hinv (fun h0 => by
    have ⟨ha, hb⟩ := hbd h0
    rw [bv32_xor1_shr1_toNat, bv32_xor1_shr1_toNat]
    exact ⟨ha, hb⟩) hm (fun ret hdr' g' aw' ht' m' hfr hext hsz hinv' hoom1 hoom0 heval hm' => ?_)
  c0_hsteps
  refine hQ (ret ^^^ 1#32) hdr' g' aw' ht' m' hfr hext hsz hinv' hoom1 hoom0 (fun h0' => ?_) hm'
  have ⟨hret, hev⟩ := heval h0'
  rw [bv32_xor1_shr1_toNat]
  refine ⟨hret, fun ρ => ?_⟩
  rw [evalLit_ofBv_xor1, hev ρ, evalLit_ofBv_xor1, evalLit_ofBv_xor1]
  dsimp only
  rw [aigBin_eval_or]

theorem bv_aig_xor_wp (Γ : Env)
    (hMkAnd : ∀ xs m Q X, bvMkAndSpec xs m Q X →
      Γ "bv_mk_and" [i64, i32, i32] [i32] xs m Q X) :
    ∀ xs m Q X, bvAigXorSpec xs m Q X → Func.wp Γ bv_aig_xor_body xs m Q X := by
  rintro ⟨h, a, b, ⟨⟩⟩ m Q X ⟨hdr, g, aw, ht, R, hinv, hbd, hm, hQ⟩
  c0_hstraight
  dsimp only
  refine bv_mk_and_step hMkAnd a b hinv hbd hm
    (fun r1 hdr1 g1 aw1 ht1 m1 hfr1 hext1 hsz1 hinv1 hoom1_1 hoom0_1 heval1 hm1 => ?_)
  c0_hstraight
  dsimp only
  refine bv_mk_and_step hMkAnd (a ^^^ 1#32) (b ^^^ 1#32) hinv1 (fun h1 => by
    have h0 : hdr.oom = 0#32 := Classical.byContradiction fun hne => hoom1_1 hne h1
    have ⟨ha, hb⟩ := hbd h0
    have hle : hdr.aig_len.toNat ≤ hdr1.aig_len.toNat := by
      rw [hinv.aig_len_eq, hinv1.aig_len_eq]; have := hext1.1; have := hext1.2.1; omega
    rw [bv32_xor1_shr1_toNat, bv32_xor1_shr1_toNat]
    exact ⟨Nat.lt_of_lt_of_le ha hle, Nat.lt_of_lt_of_le hb hle⟩) hm1
    (fun r2 hdr2 g2 aw2 ht2 m2 hfr2 hext2 hsz2 hinv2 hoom1_2 hoom0_2 heval2 hm2 => ?_)
  c0_hstraight
  dsimp only
  refine bv_mk_and_step hMkAnd (r1 ^^^ 1#32) (r2 ^^^ 1#32) hinv2 (fun h2 => by
    have h1 : hdr1.oom = 0#32 := Classical.byContradiction fun hne => hoom1_2 hne h2
    have hle : hdr1.aig_len.toNat ≤ hdr2.aig_len.toNat := by
      rw [hinv1.aig_len_eq, hinv2.aig_len_eq]; have := hext2.1; have := hext2.2.1; omega
    rw [bv32_xor1_shr1_toNat, bv32_xor1_shr1_toNat]
    exact ⟨Nat.lt_of_lt_of_le (heval1 h1).1 hle, (heval2 h2).1⟩) hm2
    (fun r3 hdr3 g3 aw3 ht3 m3 hfr3 hext3 hsz3 hinv3 hoom1_3 hoom0_3 heval3 hm3 => ?_)
  c0_hsteps
  refine hQ r3 hdr3 g3 aw3 ht3 m3 ((hfr1.trans hfr2).trans hfr3)
    (Aig.extends_trans (Aig.extends_trans hext1 hext2) hext3)
    (by omega) hinv3 (fun hne => hoom1_3 (hoom1_2 (hoom1_1 hne))) ?_ (fun h3 => ?_) hm3
  · intro h0 hcap hmax
    have h1 := hoom0_1 h0 (by omega) (by omega)
    have h2 := hoom0_2 h1 (by rw [hfr1.aig_cap, ← hext1.1]; omega) (by omega)
    exact hoom0_3 h2
      (by rw [hfr2.aig_cap, hfr1.aig_cap, ← hext2.1, ← hext1.1]; omega) (by omega)
  · have h2 : hdr2.oom = 0#32 := Classical.byContradiction fun hne => hoom1_3 hne h3
    have h1 : hdr1.oom = 0#32 := Classical.byContradiction fun hne => hoom1_2 hne h2
    have h0 : hdr.oom = 0#32 := Classical.byContradiction fun hne => hoom1_1 hne h1
    have ⟨ha, hb⟩ := hbd h0
    have ha' : ((UInt32.ofBitVec a) >>> 1).toNat < g.A + 1 + g.nodes.size := by
      rw [u32_ofBv_shr1_toNat, ← hinv.aig_len_eq]; exact ha
    have hb' : ((UInt32.ofBitVec b) >>> 1).toNat < g.A + 1 + g.nodes.size := by
      rw [u32_ofBv_shr1_toNat, ← hinv.aig_len_eq]; exact hb
    have hr1' : ((UInt32.ofBitVec r1) >>> 1).toNat < g1.A + 1 + g1.nodes.size := by
      rw [u32_ofBv_shr1_toNat, ← hinv1.aig_len_eq]; exact (heval1 h1).1
    refine ⟨(heval3 h3).1, fun ρ => ?_⟩
    rw [(heval3 h3).2 ρ, evalLit_ofBv_xor1, evalLit_ofBv_xor1,
      Aig.evalLit_extend_node hext2 hr1', (heval1 h1).2 ρ, (heval2 h2).2 ρ,
      evalLit_ofBv_xor1, evalLit_ofBv_xor1,
      Aig.evalLit_extend_node hext1 ha', Aig.evalLit_extend_node hext1 hb']
    dsimp only
    rw [aigBin_eval_xor]

theorem bv_aig_beq_wp (Γ : Env)
    (hXor : ∀ xs m Q X, bvAigXorSpec xs m Q X →
      Γ "bv_aig_xor" [i64, i32, i32] [i32] xs m Q X) :
    ∀ xs m Q X, bvAigBeqSpec xs m Q X → Func.wp Γ bv_aig_beq_body xs m Q X := by
  rintro ⟨h, a, b, ⟨⟩⟩ m Q X ⟨hdr, g, aw, ht, R, hinv, hbd, hm, hQ⟩
  c0_call hXor
  refine ⟨hdr, g, aw, ht, R, hinv, hbd, hm,
    fun ret hdr' g' aw' ht' m' hfr hext hsz hinv' hoom1 hoom0 heval hm' => ?_⟩
  c0_hsteps
  refine hQ (ret ^^^ 1#32) hdr' g' aw' ht' m' hfr hext hsz hinv' hoom1 hoom0 (fun h0' => ?_) hm'
  have ⟨hret, hev⟩ := heval h0'
  rw [bv32_xor1_shr1_toNat]
  refine ⟨hret, fun ρ => ?_⟩
  rw [evalLit_ofBv_xor1, hev ρ]
  dsimp only
  rw [aigBin_eval_beq]

theorem bv_aig_ite_wp (Γ : Env)
    (hMkAnd : ∀ xs m Q X, bvMkAndSpec xs m Q X →
      Γ "bv_mk_and" [i64, i32, i32] [i32] xs m Q X) :
    ∀ xs m Q X, bvAigIteSpec xs m Q X → Func.wp Γ bv_aig_ite_body xs m Q X := by
  rintro ⟨h, c, t, f, ⟨⟩⟩ m Q X ⟨hdr, g, aw, ht, R, hinv, hbd, hm, hQ⟩
  c0_hstraight; c0_hsplit
  · have hc1 : c = 1#32 := by c0_bv_omega [hc]
    subst hc1; c0_hsteps
    exact hQ t hdr g aw ht m (BVHdrState.AigFrame.rfl hdr) (Aig.extends_rfl g) (by omega)
      hinv (fun h => h) (fun h0 _ _ => h0)
      (fun h0 => ⟨(hbd h0).2.1, fun ρ => by simp⟩) hm
  clear hc; c0_hstraight; c0_hsplit
  · have hc0 : c = 0#32 := by c0_bv_omega [hc]
    subst hc0; c0_hsteps
    exact hQ f hdr g aw ht m (BVHdrState.AigFrame.rfl hdr) (Aig.extends_rfl g) (by omega)
      hinv (fun h => h) (fun h0 _ _ => h0)
      (fun h0 => ⟨(hbd h0).2.2, fun ρ => by simp⟩) hm
  clear hc; c0_hstraight; c0_hsplit
  · have htf : t = f := by c0_bv_omega [hc]
    subst htf; c0_hsteps
    refine hQ t hdr g aw ht m (BVHdrState.AigFrame.rfl hdr) (Aig.extends_rfl g) (by omega)
      hinv (fun h => h) (fun h0 _ _ => h0) (fun h0 => ⟨(hbd h0).2.1, fun ρ => ?_⟩) hm
    cases g.evalLit ρ (UInt32.ofBitVec c) <;> rfl
  clear hc; c0_hstraight
  dsimp only
  refine bv_mk_and_step hMkAnd c t hinv (fun h0 => ⟨(hbd h0).1, (hbd h0).2.1⟩) hm
    (fun r1 hdr1 g1 aw1 ht1 m1 hfr1 hext1 hsz1 hinv1 hoom1_1 hoom0_1 heval1 hm1 => ?_)
  c0_hstraight
  dsimp only
  refine bv_mk_and_step hMkAnd (c ^^^ 1#32) f hinv1 (fun h1 => by
    have h0 : hdr.oom = 0#32 := Classical.byContradiction fun hne => hoom1_1 hne h1
    have ⟨hc_bd, _, hf_bd⟩ := hbd h0
    have hle : hdr.aig_len.toNat ≤ hdr1.aig_len.toNat := by
      rw [hinv.aig_len_eq, hinv1.aig_len_eq]; have := hext1.1; have := hext1.2.1; omega
    rw [bv32_xor1_shr1_toNat]
    exact ⟨Nat.lt_of_lt_of_le hc_bd hle, Nat.lt_of_lt_of_le hf_bd hle⟩) hm1
    (fun r2 hdr2 g2 aw2 ht2 m2 hfr2 hext2 hsz2 hinv2 hoom1_2 hoom0_2 heval2 hm2 => ?_)
  c0_hstraight
  dsimp only
  refine bv_mk_and_step hMkAnd (r1 ^^^ 1#32) (r2 ^^^ 1#32) hinv2 (fun h2 => by
    have h1 : hdr1.oom = 0#32 := Classical.byContradiction fun hne => hoom1_2 hne h2
    have hle : hdr1.aig_len.toNat ≤ hdr2.aig_len.toNat := by
      rw [hinv1.aig_len_eq, hinv2.aig_len_eq]; have := hext2.1; have := hext2.2.1; omega
    rw [bv32_xor1_shr1_toNat, bv32_xor1_shr1_toNat]
    exact ⟨Nat.lt_of_lt_of_le (heval1 h1).1 hle, (heval2 h2).1⟩) hm2
    (fun r3 hdr3 g3 aw3 ht3 m3 hfr3 hext3 hsz3 hinv3 hoom1_3 hoom0_3 heval3 hm3 => ?_)
  c0_hsteps
  refine hQ (r3 ^^^ 1#32) hdr3 g3 aw3 ht3 m3 ((hfr1.trans hfr2).trans hfr3)
    (Aig.extends_trans (Aig.extends_trans hext1 hext2) hext3)
    (by omega) hinv3 (fun hne => hoom1_3 (hoom1_2 (hoom1_1 hne))) ?_ (fun h3 => ?_) hm3
  · intro h0 hcap hmax
    have h1 := hoom0_1 h0 (by omega) (by omega)
    have h2 := hoom0_2 h1 (by rw [hfr1.aig_cap, ← hext1.1]; omega) (by omega)
    exact hoom0_3 h2
      (by rw [hfr2.aig_cap, hfr1.aig_cap, ← hext2.1, ← hext1.1]; omega) (by omega)
  · have h2 : hdr2.oom = 0#32 := Classical.byContradiction fun hne => hoom1_3 hne h3
    have h1 : hdr1.oom = 0#32 := Classical.byContradiction fun hne => hoom1_2 hne h2
    have h0 : hdr.oom = 0#32 := Classical.byContradiction fun hne => hoom1_1 hne h1
    have ⟨hc_bd, _, hf_bd⟩ := hbd h0
    have hc' : ((UInt32.ofBitVec c) >>> 1).toNat < g.A + 1 + g.nodes.size := by
      rw [u32_ofBv_shr1_toNat, ← hinv.aig_len_eq]; exact hc_bd
    have hf' : ((UInt32.ofBitVec f) >>> 1).toNat < g.A + 1 + g.nodes.size := by
      rw [u32_ofBv_shr1_toNat, ← hinv.aig_len_eq]; exact hf_bd
    have hr1' : ((UInt32.ofBitVec r1) >>> 1).toNat < g1.A + 1 + g1.nodes.size := by
      rw [u32_ofBv_shr1_toNat, ← hinv1.aig_len_eq]; exact (heval1 h1).1
    rw [bv32_xor1_shr1_toNat]
    refine ⟨(heval3 h3).1, fun ρ => ?_⟩
    rw [evalLit_ofBv_xor1, (heval3 h3).2 ρ, evalLit_ofBv_xor1, evalLit_ofBv_xor1,
      Aig.evalLit_extend_node hext2 hr1', (heval1 h1).2 ρ, (heval2 h2).2 ρ,
      evalLit_ofBv_xor1, Aig.evalLit_extend_node hext1 hc', Aig.evalLit_extend_node hext1 hf',
      aigBin_eval_ite]

theorem bv_lits_mark_wp (Γ : Env) :
    ∀ xs m Q X, bvLitsMarkSpec xs m Q X → Func.wp Γ bv_lits_mark_body xs m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨hdr, R, hm, hQ⟩
  c0_hsteps
  exact hQ

theorem bv_lits_release_wp (Γ : Env) :
    ∀ xs m Q X, bvLitsReleaseSpec xs m Q X → Func.wp Γ bv_lits_release_body xs m Q X := by
  rintro ⟨h, mark, ⟨⟩⟩ m Q X ⟨hdr, R, hm, hQ⟩
  c0_hsteps
  · rw [aig_ite_t (by c0_bv_omega [hc])] at hQ
    exact hQ m hm
  · rw [aig_ite_f (by c0_bv_omega [hc]), bv_lits_release_hdr_eq hdr] at hQ
    exact hQ m hm

theorem bv_lits_alloc_wp (Γ : Env) :
    ∀ xs m Q X, bvLitsAllocSpec xs m Q X → Func.wp Γ bv_lits_alloc_body xs m Q X := by
  rintro ⟨h, count, ⟨⟩⟩ m Q X ⟨hdr, R, hm, hQ⟩
  c0_hstraight; c0_hsplit
  · have hoom_ne : hdr.oom ≠ 0#32 := by c0_bv_omega [hc]
    c0_hsteps
    rw [aig_ite_f (fun ⟨h0, _⟩ => hoom_ne h0)] at hQ
    dsimp only at hQ
    rw [aig_ite_t hoom_ne] at hQ
    have hhdr : { hdr with oom := hdr.oom } = hdr := by cases hdr; rfl
    rw [hhdr] at hQ
    exact hQ m hm
  have hoom0 : hdr.oom = 0#32 := by c0_bv_omega [hc]
  clear hc
  c0_hstraight
  refine wp_join0
    (fun m_oom => m_oom = m ∧
      ¬ (hdr.lits_len.toNat ≤ hdr.lits_cap.toNat ∧
        count.toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat))
    ?_ ?_
  · intro _ m_oom ⟨hm_oom, hbad⟩
    subst hm_oom
    c0_hsteps
    rw [aig_ite_f (fun ⟨_, h1, h2⟩ => hbad ⟨h1, h2⟩)] at hQ
    dsimp only at hQ
    rw [aig_ite_f (by intro h; exact h hoom0)] at hQ
    exact hQ m hm
  · intro Joom hJoom
    c0_hstraight; c0_hsplit
    · have hgt : ¬ hdr.lits_len.toNat ≤ hdr.lits_cap.toNat := by c0_bv_omega [hc]
      c0_hsteps
      exact hJoom m ⟨rfl, fun ⟨h1, _⟩ => hgt h1⟩
    have hle1 : hdr.lits_len.toNat ≤ hdr.lits_cap.toNat := by c0_bv_omega [hc]
    clear hc; c0_hstraight; c0_hsplit
    · have hgt : ¬ count.toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat := by
        c0_bv_omega [hc, hle1]
      c0_hsteps
      exact hJoom m ⟨rfl, fun ⟨_, h2⟩ => hgt h2⟩
    have hle2 : count.toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat := by
      c0_bv_omega [hc, hle1]
    clear hc hJoom
    c0_hsteps
    have hadd : (hdr.lits_len.setWidth 64 + count.setWidth 64).setWidth 32 =
        hdr.lits_len + count := by
      apply BitVec.eq_of_toNat_eq; c0_bv_omega
    have hret : (hdr.lits_len.setWidth 64).setWidth 32 = hdr.lits_len := by
      apply BitVec.eq_of_toNat_eq; c0_bv_omega
    rw [hadd] at hm
    rw [hret]
    rw [aig_ite_t ⟨hoom0, hle1, hle2⟩] at hQ
    exact hQ m hm

end

end LeanQbe.T.Examples.Bitblast.Proof
