/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Bitblast.Proof.Specs
public import LeanQbe.T.Examples.Bitblast.Proof.DriverHelpers
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.MemLemmas

/-!
# Core Evaluator Helpers (`Bitblast.Proof.Driver0Helpers`)

Factored `wp_while_state` invariants, `bv_lits_alloc` OOM/ok lemmas, and pure `BlastEvalInv` /
`NodeDenotes` step/post helpers for `Driver0.bv_eval_ops_core_wp` (keeps `<= 420` theorem lines).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Bitblast.Proof

open Std Std.Tactic.BVDecide
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Bitblast.Src
open LeanQbe.T.Examples.Bitblast.Src.Driver
open LeanQbe.T.Examples.Bitblast.Ref
open LeanQbe.T.Examples.Bitblast.Ref.BVProg

public section

abbrev BvEvalSubQ (cfg : BVWorkspaceCfg) (progPtr : BitVec 64) (progBytes : List UInt8)
    (vars : BinTree VarEntry) (cwords : BinTree Nat) (nodes : BinTree ProgNode)
    (prog : BVLogicalExpr) (hdr : BVHdrState) (g : Aig)
    (atomBases : List (BitVec 32)) (nodeIdx : BitVec 32) (R : Mem 64 → Prop)
    (Q : Post [.bool]) : Prop :=
  ∀ (ret : Bool) (hdr' : BVHdrState) (g' : Aig) (sliceOffs' : List (BitVec 32))
    (aigWords' : List (BitVec 64)) (htSlots' litsPool' : List (BitVec 32)) (m' : Mem 64),
    BVWorkspaceOk cfg hdr' atomBases sliceOffs' aigWords' htSlots' litsPool' →
    AigInv hdr' g' aigWords' htSlots' → g ≤ g' →
    hdr'.prog_ptr = progPtr →
    hdr'.n_cwords = hdr.n_cwords → hdr'.root_node = hdr.root_node →
    (ret = true → hdr'.oom = 0#32 ∧ BlastEvalInv cfg progPtr progBytes vars cwords nodes prog
      hdr' g' atomBases sliceOffs' aigWords' htSlots' litsPool' (nodeIdx.toNat + 1)) →
    (bytes progPtr progBytes ⋆
      bvBlastMem cfg hdr' atomBases sliceOffs' aigWords' htSlots' litsPool' ⋆ R) m' →
    Q (ret, ⟨⟩) m'

@[expose] def drv0VarInv (cfg : BVWorkspaceCfg) (progPtr : BitVec 64) (progBytes : List UInt8)
    (hdr hdr1 : BVHdrState) (atomBases sliceOffs : List (BitVec 32))
    (aigWords : List (BitVec 64)) (htSlots litsPool : List (BitVec 32))
    (R : Mem 64 → Prop) (w a : Nat) (s : Nat × List (BitVec 32)) (ml : Mem 64) : Prop :=
  s.1 ≤ w ∧ s.2.length = cfg.lits_cap ∧
  (∀ p < hdr.lits_len.toNat, s.2.getD p 0#32 = litsPool.getD p 0#32) ∧
  (∀ p < s.1, s.2.getD (hdr.lits_len.toNat + p) 0#32 =
    BitVec.ofNat 32 (countAtoms progBytes a + p) <<< 1) ∧
  (bytes progPtr progBytes ⋆ bvBlastMem cfg hdr1 atomBases sliceOffs aigWords
    htSlots s.2 ⋆ R) ml

@[expose] def drv0ConstInv (cfg : BVWorkspaceCfg) (progPtr : BitVec 64) (progBytes : List UInt8)
    (hdr hdr1 : BVHdrState) (atomBases sliceOffs : List (BitVec 32))
    (aigWords : List (BitVec 64)) (htSlots litsPool : List (BitVec 32))
    (R : Mem 64 → Prop) (w a : Nat) (s : Nat × BitVec 32 × List (BitVec 32))
    (ml : Mem 64) : Prop :=
  s.1 ≤ w ∧
  (0 < s.1 → s.2.1.toNat = u32At progBytes (cwordsOff cfg.n_vars + a + (s.1 - 1) / 32)) ∧
  s.2.2.length = cfg.lits_cap ∧
  (∀ p < hdr.lits_len.toNat, s.2.2.getD p 0#32 = litsPool.getD p 0#32) ∧
  (∀ p < s.1, s.2.2.getD (hdr.lits_len.toNat + p) 0#32 =
    BitVec.ofNat 32 (if (u32At progBytes
      (cwordsOff cfg.n_vars + a + p / 32)).testBit (p % 32) then 1 else 0)) ∧
  (bytes progPtr progBytes ⋆ bvBlastMem cfg hdr1 atomBases sliceOffs aigWords
    htSlots s.2.2 ⋆ R) ml

def drv0NotInv (cfg : BVWorkspaceCfg) (progPtr : BitVec 64) (progBytes : List UInt8)
    (hdr hdr1 : BVHdrState) (atomBases sliceOffs : List (BitVec 32))
    (aigWords : List (BitVec 64)) (htSlots litsPool : List (BitVec 32))
    (R : Mem 64 → Prop) (w : Nat) (a_off : BitVec 32)
    (s : Nat × List (BitVec 32)) (ml : Mem 64) : Prop :=
  s.1 ≤ w ∧ s.2.length = cfg.lits_cap ∧
  (∀ p < hdr.lits_len.toNat, s.2.getD p 0#32 = litsPool.getD p 0#32) ∧
  (∀ p < s.1, s.2.getD (hdr.lits_len.toNat + p) 0#32 =
    litsPool.getD (a_off.toNat + p) 0#32 ^^^ 1#32) ∧
  (bytes progPtr progBytes ⋆ bvBlastMem cfg hdr1 atomBases sliceOffs aigWords
    htSlots s.2 ⋆ R) ml

def drv0EqInv (cfg : BVWorkspaceCfg) (progPtr : BitVec 64) (progBytes : List UInt8)
    (hdr : BVHdrState) (g : Aig) (atomBases sliceOffs litsPool : List (BitVec 32))
    (R : Mem 64 → Prop) (ew : Nat) (ea eb : BVExpr ew)
    (s : Nat × BitVec 32 × BVHdrState × Aig × List (BitVec 64) × List (BitVec 32))
    (ml : Mem 64) : Prop :=
  s.1 ≤ ew ∧ s.2.2.1.oom = 0#32 ∧
  BVWorkspaceOk cfg s.2.2.1 atomBases sliceOffs s.2.2.2.2.1 s.2.2.2.2.2 litsPool ∧
  AigInv s.2.2.1 s.2.2.2.1 s.2.2.2.2.1 s.2.2.2.2.2 ∧
  g ≤ s.2.2.2.1 ∧
  s.2.2.1.prog_ptr = progPtr ∧ s.2.2.1.n_cwords = hdr.n_cwords ∧
  s.2.2.1.root_node = hdr.root_node ∧ s.2.2.1.lits_len = hdr.lits_len ∧
  (s.2.1 >>> 1).toNat < s.2.2.1.aig_len.toNat ∧
  (∀ assign : BVExpr.Assignment,
    s.2.2.2.1.evalLit (atomAssign progBytes assign) (UInt32.ofBitVec s.2.1) =
      decide (∀ p < s.1, (ea.eval assign).getLsbD p = (eb.eval assign).getLsbD p)) ∧
  (bytes progPtr progBytes ⋆ bvBlastMem cfg s.2.2.1 atomBases sliceOffs
    s.2.2.2.2.1 s.2.2.2.2.2 litsPool ⋆ R) ml

end

public section

theorem drv0_lits_alloc_cond_ok {cfg : BVWorkspaceCfg} {hdr : BVHdrState}
    {ab so : List (BitVec 32)} {aw : List (BitVec 64)} {ht lp : List (BitVec 32)}
    {w : Nat} (hok : BVWorkspaceOk cfg hdr ab so aw ht lp) (hoom0 : hdr.oom = 0#32)
    (hl_cap : hdr.lits_len.toNat ≤ cfg.lits_cap) (hw_lt : w < 2 ^ 32)
    (hfit : w ≤ cfg.lits_cap - hdr.lits_len.toNat) :
    (hdr.oom = 0#32 ∧ hdr.lits_len.toNat ≤ hdr.lits_cap.toNat ∧
      (BitVec.ofNat 32 w).toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat) ∧
    ({ hdr with lits_len := hdr.lits_len + BitVec.ofNat 32 w } : BVHdrState).lits_len.toNat =
      hdr.lits_len.toNat + w := by
  have hc : hdr.oom = 0#32 ∧ hdr.lits_len.toNat ≤ hdr.lits_cap.toNat ∧
      (BitVec.ofNat 32 w).toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat := by
    rw [hok.hdr_lcap, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hok.lcap_lt,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw_lt]
    exact ⟨hoom0, hl_cap, hfit⟩
  have hlen :
      ({ hdr with lits_len := hdr.lits_len + BitVec.ofNat 32 w } : BVHdrState).lits_len.toNat =
        hdr.lits_len.toNat + w := by
    have := hok.lcap_lt
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw_lt,
      Nat.mod_eq_of_lt (by omega : hdr.lits_len.toNat + w < 2 ^ 32)]
  exact ⟨hc, hlen⟩

theorem drv0_lits_alloc_oom_cond {cfg : BVWorkspaceCfg} {hdr : BVHdrState}
    {ab so : List (BitVec 32)} {aw : List (BitVec 64)} {ht lp : List (BitVec 32)}
    {w : Nat} (hok : BVWorkspaceOk cfg hdr ab so aw ht lp) (hw_lt : w < 2 ^ 32)
    (hnot : ¬ w ≤ cfg.lits_cap - hdr.lits_len.toNat) :
    ¬ (hdr.oom = 0#32 ∧ hdr.lits_len.toNat ≤ hdr.lits_cap.toNat ∧
      (BitVec.ofNat 32 w).toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat) := by
  rw [hok.hdr_lcap, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hok.lcap_lt,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw_lt]
  omega

theorem drv0_var_step {progBytes : List UInt8} {cfg : BVWorkspaceCfg}
    {hdr hdr1 : BVHdrState} {ab lp0 lp : List (BitVec 32)} {a w j : Nat}
    (ha32 : (BitVec.ofNat 32 a).toNat < ab.length)
    (ha_idx_get : ab[(BitVec.ofNat 32 a).toNat]'ha32 = ab.getD a 0#32)
    (hab_eq : (ab.getD a 0#32).toNat = countAtoms progBytes a)
    (hl_cap : hdr.lits_len.toNat ≤ cfg.lits_cap) (hlcap_lt : cfg.lits_cap < 2 ^ 32)
    (hfit : w ≤ cfg.lits_cap - hdr.lits_len.toNat) (hj_lt : j < w) (hw_lt : w < 2 ^ 32)
    (hlp_len : lp.length = cfg.lits_cap)
    (hcnt_a1 : countAtoms progBytes (a + 1) ≤ countAtoms progBytes cfg.n_vars)
    (hw_var : u32At progBytes (8 + 2 * a + 1) = w)
    (hcnt_prev : countAtoms progBytes a + u32At progBytes (8 + 2 * a + 1) =
      countAtoms progBytes (a + 1))
    (hcnt_lt : countAtoms progBytes cfg.n_vars < bvDimacsBound)
    (hagree : ∀ p < hdr.lits_len.toNat, lp.getD p 0#32 = lp0.getD p 0#32)
    (hset : ∀ p < j, lp.getD (hdr.lits_len.toNat + p) 0#32 =
      BitVec.ofNat 32 (countAtoms progBytes a + p) <<< 1)
    (_hh1 : hdr1 = { hdr with lits_len := hdr.lits_len + BitVec.ofNat 32 w }) :
    (hdr.lits_len + BitVec.ofNat 32 j).toNat = hdr.lits_len.toNat + j ∧
    (hdr.lits_len + BitVec.ofNat 32 j).toNat < lp.length ∧
    BitVec.ofNat 32 j + 1 = BitVec.ofNat 32 (j + 1) ∧
    (∀ p < hdr.lits_len.toNat,
      (lp.set (hdr.lits_len + BitVec.ofNat 32 j).toNat
        ((ab[(BitVec.ofNat 32 a).toNat]'ha32 + BitVec.ofNat 32 j) <<< (1 : Nat))).getD p 0#32 =
        lp0.getD p 0#32) ∧
    (∀ p < j + 1,
      (lp.set (hdr.lits_len + BitVec.ofNat 32 j).toNat
        ((ab[(BitVec.ofNat 32 a).toNat]'ha32 + BitVec.ofNat 32 j) <<< (1 : Nat))).getD
          (hdr.lits_len.toNat + p) 0#32 = BitVec.ofNat 32 (countAtoms progBytes a + p) <<< 1) := by
  have hj32 : j < 2 ^ 32 := Nat.lt_trans hj_lt hw_lt
  have hidx_eq : (hdr.lits_len + BitVec.ofNat 32 j).toNat = hdr.lits_len.toNat + j := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj32,
      Nat.mod_eq_of_lt (by omega : hdr.lits_len.toNat + j < 2 ^ 32)]
  have hidx_lt : (hdr.lits_len + BitVec.ofNat 32 j).toNat < lp.length := by
    rw [hlp_len, hidx_eq]; omega
  have hj_eq32 : BitVec.ofNat 32 j + 1 = BitVec.ofNat 32 (j + 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl,
      Nat.mod_eq_of_lt hj32, Nat.mod_eq_of_lt (by omega : j + 1 < 2 ^ 32)]
  have hval : ((ab[(BitVec.ofNat 32 a).toNat]'ha32 + BitVec.ofNat 32 j) <<< (1 : Nat)) =
      BitVec.ofNat 32 (countAtoms progBytes a + j) <<< 1 := by
    unfold bvDimacsBound at hcnt_lt
    have hax : countAtoms progBytes a + j < 2 ^ 32 := by omega
    rw [ha_idx_get]; congr 1; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, hab_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hj32, Nat.mod_eq_of_lt hax]
  refine ⟨hidx_eq, hidx_lt, hj_eq32, fun p hp_lt => ?_, fun p hp_lt => ?_⟩
  · rw [list_getD_set_ne _ _ _ (by omega)]; exact hagree p hp_lt
  · by_cases hpj : p = j
    · subst hpj; rw [hidx_eq, list_getD_set_self _ _ _ (by rw [hlp_len]; omega), hval]
    · rw [list_getD_set_ne _ _ _ (by omega)]; exact hset p (by omega)

theorem drv0_var_post {cfg : BVWorkspaceCfg} {progPtr : BitVec 64} {progBytes : List UInt8}
    {vars : BinTree VarEntry} {cwords : BinTree Nat} {nodes : BinTree ProgNode}
    {prog : BVLogicalExpr} {hdr hdr1 : BVHdrState} {g : Aig}
    {atomBases sliceOffs : List (BitVec 32)} {aigWords : List (BitVec 64)}
    {htSlots litsPool lp : List (BitVec 32)} {nodeIdx : BitVec 32} {a w : Nat}
    {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post [.bool]}
    (hoom0 : hdr.oom = 0#32) (hni_lt : nodeIdx.toNat < cfg.n_nodes)
    (hok : BVWorkspaceOk cfg hdr atomBases sliceOffs aigWords htSlots litsPool)
    (haig : AigInv hdr g aigWords htSlots)
    (hinv : BlastEvalInv cfg progPtr progBytes vars cwords nodes prog hdr g
      atomBases sliceOffs aigWords htSlots litsPool nodeIdx.toNat)
    (hfit : w ≤ cfg.lits_cap - hdr.lits_len.toNat) (ha_nv : a < cfg.n_vars)
    (hw_var : u32At progBytes (8 + 2 * a + 1) = w)
    (hnd_var : nodes.get? nodeIdx.toNat = some (.bv w (.var (u32At progBytes (8 + 2 * a)))))
    (hh1 : hdr1 = { hdr with lits_len := hdr.lits_len + BitVec.ofNat 32 w })
    (hl1_len : hdr1.lits_len.toNat = hdr.lits_len.toNat + w)
    (hlp_len : lp.length = cfg.lits_cap)
    (hagree : ∀ p < hdr.lits_len.toNat, lp.getD p 0#32 = litsPool.getD p 0#32)
    (hset : ∀ p < w, lp.getD (hdr.lits_len.toNat + p) 0#32 =
      BitVec.ofNat 32 (countAtoms progBytes a + p) <<< 1)
    (hm_fin : (bytes progPtr progBytes ⋆ bvBlastMem cfg hdr1 atomBases
      (sliceOffs.set nodeIdx.toNat hdr.lits_len) aigWords htSlots lp ⋆ R) m')
    (hQ : BvEvalSubQ cfg progPtr progBytes vars cwords nodes prog hdr g atomBases nodeIdx R Q) :
    Q (true, ⟨⟩) m' := by
  subst hh1
  have haig1 := aigInv_set_litsLen (hdr.lits_len + BitVec.ofNat 32 w) haig
  have hok1 := bvWorkspaceOk_set_litsLen (hdr.lits_len + BitVec.ofNat 32 w) hok
  have hok2 := BVWorkspaceOk.set_litsPool hlp_len
    (BVWorkspaceOk.set_sliceOffs nodeIdx.toNat hdr.lits_len hok1)
  have hcnt_n := hinv.parsed.valid.atoms_ok
  have hcnt_a1 : countAtoms progBytes (a + 1) ≠ 0 ∧
      countAtoms progBytes (a + 1) ≤ countAtoms progBytes cfg.n_vars :=
    countAtoms_mono_ne_zero (by omega : a + 1 ≤ cfg.n_vars) (hinv.nv_eq ▸ hcnt_n)
  have hcnt_prev := countAtoms_prev_ne_zero hcnt_a1.1
  have hcnt_lt := countAtoms_lt progBytes (u32At progBytes 2)
  have hl_cap' := hinv.lits_le_cap
  refine hQ true _ g (sliceOffs.set nodeIdx.toNat hdr.lits_len) aigWords htSlots lp _
    hok2 haig1 (Aig.extends_rfl g) hinv.prog_ptr_eq rfl rfl
    (fun _ => ⟨hoom0, ?_⟩) hm_fin
  refine blastEvalInv_step hoom0 hinv hok2 haig1 (Aig.extends_rfl g) hni_lt hinv.prog_ptr_eq
    rfl rfl (by rw [hl1_len]; omega) (by rw [hl1_len]; omega) hagree ?_
  refine nodeDenotes_set_bv hnd_var (by rw [hl1_len]; omega) (fun k hk => ?_)
    (fun assign => ?_) (by rw [hok.so_len]; exact hni_lt)
  · rw [hset k hk]
    have hlt_a := hcnt_lt; rw [← hinv.nv_eq] at hlt_a
    have hax : countAtoms progBytes a + k < 2 ^ 31 := by
      have := hcnt_prev.2.2; have := hcnt_a1.2; unfold bvDimacsBound at hlt_a; omega
    rw [bv32_shl1_atom_lsr1 hax, hinv.atoms_eq]
    have := hcnt_prev.2.2; have := hcnt_a1.2; omega
  · have hk' : hdr.lits_len.toNat + w ≤ lp.length := by rw [hlp_len]; omega
    rw [sliceDenotes_iff hk']; intro k hk
    have hlt_a2 := hcnt_lt; rw [← hinv.nv_eq] at hlt_a2
    rw [hset k hk, evalLit_shl1_atom g _ (by
      have := hcnt_prev.2.2; have := hcnt_a1.2; unfold bvDimacsBound at hlt_a2; omega)]
    have ha_bound : 1 ≤ countAtoms progBytes a + k ∧ countAtoms progBytes a + k ≤ g.A := by
      have := countAtoms_pos_of_ne_zero (hinv.nv_eq ▸ hcnt_n)
      have hpos_a := countAtoms_mono_ne_zero (Nat.zero_le a) hcnt_prev.1
      simp only [countAtoms] at hpos_a
      have := hcnt_prev.2.2; have := hcnt_a1.2; rw [hinv.atoms_eq]; omega
    rw [Aig.evalNode_atom g _ ha_bound.1 ha_bound.2,
      atomAssign_eq hcnt_n (hinv.nv_eq ▸ ha_nv) (by omega), bvExpr_var_getLsbD _ assign hk]

theorem drv0_const_step_set {progBytes : List UInt8} {cfg : BVWorkspaceCfg}
    {hdr : BVHdrState} {ab so lp0 lp : List (BitVec 32)} {aw : List (BitVec 64)}
    {ht : List (BitVec 32)} {a w j : Nat} {cw' : BitVec 32}
    (hok : BVWorkspaceOk cfg hdr ab so aw ht lp0) (hl_cap : hdr.lits_len.toNat ≤ cfg.lits_cap)
    (hfit : w ≤ cfg.lits_cap - hdr.lits_len.toNat) (hj_lt : j < w) (hw_lt : w < 2 ^ 32)
    (hlp_len : lp.length = cfg.lits_cap)
    (hcw'_eq : cw'.toNat = u32At progBytes (cwordsOff cfg.n_vars + a + j / 32))
    (hagree : ∀ p < hdr.lits_len.toNat, lp.getD p 0#32 = lp0.getD p 0#32)
    (hset : ∀ p < j, lp.getD (hdr.lits_len.toNat + p) 0#32 =
      BitVec.ofNat 32 (if (u32At progBytes
        (cwordsOff cfg.n_vars + a + p / 32)).testBit (p % 32) then 1 else 0)) :
    (hdr.lits_len + BitVec.ofNat 32 j).toNat = hdr.lits_len.toNat + j ∧
    (hdr.lits_len + BitVec.ofNat 32 j).toNat < lp.length ∧
    BitVec.ofNat 32 j + 1 = BitVec.ofNat 32 (j + 1) ∧
    (0 < j + 1 → cw'.toNat = u32At progBytes (cwordsOff cfg.n_vars + a + (j + 1 - 1) / 32)) ∧
    (∀ p < hdr.lits_len.toNat,
      (lp.set (hdr.lits_len + BitVec.ofNat 32 j).toNat
        ((cw' >>> ((BitVec.ofNat 32 j &&& 31).toNat % 32)) &&& 1)).getD p 0#32 =
        lp0.getD p 0#32) ∧
    (∀ p < j + 1,
      (lp.set (hdr.lits_len + BitVec.ofNat 32 j).toNat
        ((cw' >>> ((BitVec.ofNat 32 j &&& 31).toNat % 32)) &&& 1)).getD
          (hdr.lits_len.toNat + p) 0#32 = BitVec.ofNat 32 (if (u32At progBytes
            (cwordsOff cfg.n_vars + a + p / 32)).testBit (p % 32) then 1 else 0)) := by
  have hj32 : j < 2 ^ 32 := Nat.lt_trans hj_lt hw_lt
  have := hok.lcap_lt
  have hidx_eq : (hdr.lits_len + BitVec.ofNat 32 j).toNat = hdr.lits_len.toNat + j := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj32,
      Nat.mod_eq_of_lt (by omega : hdr.lits_len.toNat + j < 2 ^ 32)]
  have hidx_lt : (hdr.lits_len + BitVec.ofNat 32 j).toNat < lp.length := by
    rw [hlp_len, hidx_eq]; omega
  have hj_eq32 : BitVec.ofNat 32 j + 1 = BitVec.ofNat 32 (j + 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl,
      Nat.mod_eq_of_lt hj32, Nat.mod_eq_of_lt (by omega : j + 1 < 2 ^ 32)]
  have hsh_eq : (BitVec.ofNat 32 j &&& 31).toNat % 32 = j % 32 := by
    change (BitVec.ofNat 32 j &&& 31#32).toNat % 32 = j % 32
    rw [bv32_and31_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj32, Nat.mod_mod]
  have hlitv : ((cw' >>> ((BitVec.ofNat 32 j &&& 31).toNat % 32)) &&& 1) =
      BitVec.ofNat 32 (if (u32At progBytes
        (cwordsOff cfg.n_vars + a + j / 32)).testBit (j % 32) then 1 else 0) := by
    rw [hsh_eq]; change ((cw' >>> (j % 32)) &&& 1#32) = _; rw [bv32_bit_word, hcw'_eq]
  refine ⟨hidx_eq, hidx_lt, hj_eq32, fun _ => ?_, fun p hp_lt => ?_, fun p hp_lt => ?_⟩
  · have hdiv_eq : (j + 1 - 1) / 32 = j / 32 := by omega
    rw [hdiv_eq]; exact hcw'_eq
  · rw [list_getD_set_ne _ _ _ (by omega)]; exact hagree p hp_lt
  · by_cases hpj : p = j
    · subst hpj; rw [hidx_eq, list_getD_set_self _ _ _ (by rw [hlp_len]; omega), hlitv]
    · rw [list_getD_set_ne _ _ _ (by omega)]; exact hset p (by omega)

theorem drv0_const_read_idx {progBytes : List UInt8} {vars : BinTree VarEntry}
    {cwords : BinTree Nat} {nodes : BinTree ProgNode} {prog : BVLogicalExpr}
    {cfg : BVWorkspaceCfg} {progPtr : BitVec 64} {hdr : BVHdrState} {g : Aig}
    {ab so : List (BitVec 32)} {aw : List (BitVec 64)} {ht lp : List (BitVec 32)}
    {nodeIdx : BitVec 32} {a w j : Nat}
    (hinv : BlastEvalInv cfg progPtr progBytes vars cwords nodes prog hdr g
      ab so aw ht lp nodeIdx.toNat)
    (hok : BVWorkspaceOk cfg hdr ab so aw ht lp) (ha_lt : a < 4294967296)
    (hj_lt : j < w) (hw_lt : w < 4294967296)
    (hcw_bd : 0 < (w + 31) / 32 → a + (w + 31) / 32 ≤ u32At progBytes 4) :
    ((8 : BitVec 64) + (hdr.n_vars.setWidth 64 <<< 1) + (BitVec.ofNat 32 a).setWidth 64 +
        (BitVec.ofNat 32 j >>> 5).setWidth 64).toNat = cwordsOff cfg.n_vars + a + j / 32 ∧
    4 * (((8 : BitVec 64) + (hdr.n_vars.setWidth 64 <<< 1) + (BitVec.ofNat 32 a).setWidth 64 +
        (BitVec.ofNat 32 j >>> 5).setWidth 64).toNat + 1) ≤ progBytes.length := by
  have hj32 : j < 2 ^ 32 := Nat.lt_trans hj_lt hw_lt
  have hnw_pos : 0 < (w + 31) / 32 := by omega
  have hac_bd := hcw_bd hnw_pos
  have hjdiv_lt : j / 32 < (w + 31) / 32 := by omega
  have htot := hinv.parsed.valid.total_len
  have hnv_eq : hdr.n_vars = BitVec.ofNat 32 cfg.n_vars := hok.hdr_nv
  have hnv_lt := hok.nv_lt
  have hlsr : (BitVec.ofNat 32 j >>> 5).toNat = j / 32 := by
    rw [bv32_lsr5_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj32]
  have heq : ((8 : BitVec 64) + (hdr.n_vars.setWidth 64 <<< 1) + (BitVec.ofNat 32 a).setWidth 64 +
      (BitVec.ofNat 32 j >>> 5).setWidth 64).toNat = cwordsOff cfg.n_vars + a + j / 32 := by
    unfold cwordsOff
    have hn64 : (hdr.n_vars.setWidth 64 <<< 1).toNat = 2 * cfg.n_vars := by
      rw [hnv_eq, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
        Nat.shiftLeft_eq, Nat.pow_one, Nat.mod_eq_of_lt hnv_lt,
        Nat.mod_eq_of_lt (by omega : cfg.n_vars < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : cfg.n_vars * 2 < 2 ^ 64)]; omega
    have ha64 : ((BitVec.ofNat 32 a).setWidth 64).toNat = a := by
      rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt,
        Nat.mod_eq_of_lt (by omega : a < 2 ^ 64)]
    have hj64 : ((BitVec.ofNat 32 j >>> 5).setWidth 64).toNat = j / 32 := by
      rw [BitVec.toNat_setWidth, hlsr, Nat.mod_eq_of_lt (by omega : j / 32 < 2 ^ 64)]
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add,
      show (8 : BitVec 64).toNat = 8 from rfl, hn64, ha64, hj64,
      Nat.mod_eq_of_lt (by omega : 8 + 2 * cfg.n_vars < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : 8 + 2 * cfg.n_vars + a < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : 8 + 2 * cfg.n_vars + a + j / 32 < 2 ^ 64)]
  refine ⟨heq, ?_⟩
  rw [heq]
  have htot' := htot
  rw [← hinv.nv_eq, ← hinv.nn_eq] at htot'
  unfold cwordsOff; omega

theorem drv0_const_post {cfg : BVWorkspaceCfg} {progPtr : BitVec 64} {progBytes : List UInt8}
    {vars : BinTree VarEntry} {cwords : BinTree Nat} {nodes : BinTree ProgNode}
    {prog : BVLogicalExpr} {hdr hdr1 : BVHdrState} {g : Aig}
    {atomBases sliceOffs : List (BitVec 32)} {aigWords : List (BitVec 64)}
    {htSlots litsPool lp : List (BitVec 32)} {nodeIdx : BitVec 32} {a w : Nat}
    {val : BitVec w} {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post [.bool]}
    (hoom0 : hdr.oom = 0#32) (hni_lt : nodeIdx.toNat < cfg.n_nodes)
    (hok : BVWorkspaceOk cfg hdr atomBases sliceOffs aigWords htSlots litsPool)
    (haig : AigInv hdr g aigWords htSlots)
    (hinv : BlastEvalInv cfg progPtr progBytes vars cwords nodes prog hdr g
      atomBases sliceOffs aigWords htSlots litsPool nodeIdx.toNat)
    (hfit : w ≤ cfg.lits_cap - hdr.lits_len.toNat)
    (hconst_bits : ∀ k < w, val.getLsbD k =
      (u32At progBytes (cwordsOff cfg.n_vars + a + k / 32)).testBit (k % 32))
    (hnd_const : nodes.get? nodeIdx.toNat = some (.bv w (.const val)))
    (hh1 : hdr1 = { hdr with lits_len := hdr.lits_len + BitVec.ofNat 32 w })
    (hl1_len : hdr1.lits_len.toNat = hdr.lits_len.toNat + w)
    (hlp_len : lp.length = cfg.lits_cap)
    (hagree : ∀ p < hdr.lits_len.toNat, lp.getD p 0#32 = litsPool.getD p 0#32)
    (hset : ∀ p < w, lp.getD (hdr.lits_len.toNat + p) 0#32 =
      BitVec.ofNat 32 (if (u32At progBytes
        (cwordsOff cfg.n_vars + a + p / 32)).testBit (p % 32) then 1 else 0))
    (hm_fin : (bytes progPtr progBytes ⋆ bvBlastMem cfg hdr1 atomBases
      (sliceOffs.set nodeIdx.toNat hdr.lits_len) aigWords htSlots lp ⋆ R) m')
    (hQ : BvEvalSubQ cfg progPtr progBytes vars cwords nodes prog hdr g atomBases nodeIdx R Q) :
    Q (true, ⟨⟩) m' := by
  subst hh1
  have haig1 := aigInv_set_litsLen (hdr.lits_len + BitVec.ofNat 32 w) haig
  have hok1 := bvWorkspaceOk_set_litsLen (hdr.lits_len + BitVec.ofNat 32 w) hok
  have hok2 := BVWorkspaceOk.set_litsPool hlp_len
    (BVWorkspaceOk.set_sliceOffs nodeIdx.toNat hdr.lits_len hok1)
  have hl_cap' := hinv.lits_le_cap
  refine hQ true _ g (sliceOffs.set nodeIdx.toNat hdr.lits_len) aigWords htSlots lp _
    hok2 haig1 (Aig.extends_rfl g) hinv.prog_ptr_eq rfl rfl
    (fun _ => ⟨hoom0, ?_⟩) hm_fin
  refine blastEvalInv_step hoom0 hinv hok2 haig1 (Aig.extends_rfl g) hni_lt hinv.prog_ptr_eq
    rfl rfl (by rw [hl1_len]; omega) (by rw [hl1_len]; omega) hagree ?_
  refine nodeDenotes_set_bv hnd_const (by rw [hl1_len]; omega) (fun k hk => ?_)
    (fun assign => ?_) (by rw [hok.so_len]; exact hni_lt)
  · rw [hset k hk]
    cases ((u32At progBytes (cwordsOff cfg.n_vars + a + k / 32)).testBit (k % 32)) <;>
      (simp; omega)
  · have hk' : hdr.lits_len.toNat + w ≤ lp.length := by rw [hlp_len]; omega
    rw [sliceDenotes_iff hk']; intro k hk
    rw [hset k hk, evalLit_bit01 g (atomAssign progBytes assign), ← hconst_bits k hk]; rfl

theorem drv0_not_step {cfg : BVWorkspaceCfg} {hdr : BVHdrState}
    {ab so lp0 lp : List (BitVec 32)} {aw : List (BitVec 64)} {ht : List (BitVec 32)}
    {a_off : BitVec 32} {w j : Nat}
    (hok : BVWorkspaceOk cfg hdr ab so aw ht lp0) (hl_cap : hdr.lits_len.toNat ≤ cfg.lits_cap)
    (hfit : w ≤ cfg.lits_cap - hdr.lits_len.toNat) (hj_lt : j < w) (hw_lt : w < 2 ^ 32)
    (ha_off_le : a_off.toNat + w ≤ hdr.lits_len.toNat) (hlp_len : lp.length = cfg.lits_cap)
    (hagree : ∀ p < hdr.lits_len.toNat, lp.getD p 0#32 = lp0.getD p 0#32)
    (hset : ∀ p < j, lp.getD (hdr.lits_len.toNat + p) 0#32 =
      lp0.getD (a_off.toNat + p) 0#32 ^^^ 1#32) :
    ∃ ha_j_lt : (a_off + BitVec.ofNat 32 j).toNat < lp.length,
      (hdr.lits_len + BitVec.ofNat 32 j).toNat = hdr.lits_len.toNat + j ∧
      (hdr.lits_len + BitVec.ofNat 32 j).toNat < lp.length ∧
      BitVec.ofNat 32 j + 1 = BitVec.ofNat 32 (j + 1) ∧
      (∀ p < hdr.lits_len.toNat,
        (lp.set (hdr.lits_len + BitVec.ofNat 32 j).toNat
          (lp[(a_off + BitVec.ofNat 32 j).toNat]'ha_j_lt ^^^ 1#32)).getD p 0#32 =
          lp0.getD p 0#32) ∧
      (∀ p < j + 1,
        (lp.set (hdr.lits_len + BitVec.ofNat 32 j).toNat
          (lp[(a_off + BitVec.ofNat 32 j).toNat]'ha_j_lt ^^^ 1#32)).getD
            (hdr.lits_len.toNat + p) 0#32 = lp0.getD (a_off.toNat + p) 0#32 ^^^ 1#32) := by
  have hj32 : j < 2 ^ 32 := Nat.lt_trans hj_lt hw_lt
  have := hok.lcap_lt
  have ha_j_eq : (a_off + BitVec.ofNat 32 j).toNat = a_off.toNat + j := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj32,
      Nat.mod_eq_of_lt (by omega : a_off.toNat + j < 2 ^ 32)]
  have ha_j_lt : (a_off + BitVec.ofNat 32 j).toNat < lp.length := by rw [hlp_len, ha_j_eq]; omega
  have hidx_eq : (hdr.lits_len + BitVec.ofNat 32 j).toNat = hdr.lits_len.toNat + j := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj32,
      Nat.mod_eq_of_lt (by omega : hdr.lits_len.toNat + j < 2 ^ 32)]
  have hidx_lt : (hdr.lits_len + BitVec.ofNat 32 j).toNat < lp.length := by
    rw [hlp_len, hidx_eq]; omega
  have hsrc_eq : lp[(a_off + BitVec.ofNat 32 j).toNat]'ha_j_lt =
      lp0.getD (a_off.toNat + j) 0#32 := by
    rw [list_getD_eq_getElem _ 0#32, ha_j_eq]; exact hagree _ (by omega)
  have hj_eq32 : BitVec.ofNat 32 j + 1 = BitVec.ofNat 32 (j + 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl,
      Nat.mod_eq_of_lt hj32, Nat.mod_eq_of_lt (by omega : j + 1 < 2 ^ 32)]
  refine ⟨ha_j_lt, hidx_eq, hidx_lt, hj_eq32, fun p hp_lt => ?_, fun p hp_lt => ?_⟩
  · rw [list_getD_set_ne _ _ _ (by omega)]; exact hagree p hp_lt
  · by_cases hpj : p = j
    · subst hpj; rw [hidx_eq, list_getD_set_self _ _ _ (by rw [hlp_len]; omega), hsrc_eq]
    · rw [list_getD_set_ne _ _ _ (by omega)]; exact hset p (by omega)

theorem drv0_not_post {cfg : BVWorkspaceCfg} {progPtr : BitVec 64} {progBytes : List UInt8}
    {vars : BinTree VarEntry} {cwords : BinTree Nat} {nodes : BinTree ProgNode}
    {prog : BVLogicalExpr} {hdr hdr1 : BVHdrState} {g : Aig}
    {atomBases sliceOffs : List (BitVec 32)} {aigWords : List (BitVec 64)}
    {htSlots litsPool lp : List (BitVec 32)} {nodeIdx : BitVec 32} {a w : Nat}
    {ea : BVExpr w} {a_off : BitVec 32} {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post [.bool]}
    (hoom0 : hdr.oom = 0#32) (hni_lt : nodeIdx.toNat < cfg.n_nodes)
    (hok : BVWorkspaceOk cfg hdr atomBases sliceOffs aigWords htSlots litsPool)
    (haig : AigInv hdr g aigWords htSlots)
    (hinv : BlastEvalInv cfg progPtr progBytes vars cwords nodes prog hdr g
      atomBases sliceOffs aigWords htSlots litsPool nodeIdx.toNat)
    (hfit : w ≤ cfg.lits_cap - hdr.lits_len.toNat)
    (ha_get : a_off = sliceOffs.getD a 0#32)
    (ha_bd : ∀ k < w, (litsPool.getD ((sliceOffs.getD a 0#32).toNat + k) 0#32 >>> 1).toNat <
      g.A + 1 + g.nodes.size)
    (ha_sd : ∀ assign : BVExpr.Assignment, SliceDenotes g (atomAssign progBytes assign)
      (litsSlice litsPool (sliceOffs.getD a 0#32).toNat w) (ea.eval assign))
    (hnd_not : nodes.get? nodeIdx.toNat = some (.bv w (.un .not ea)))
    (hh1 : hdr1 = { hdr with lits_len := hdr.lits_len + BitVec.ofNat 32 w })
    (hl1_len : hdr1.lits_len.toNat = hdr.lits_len.toNat + w)
    (hlp_len : lp.length = cfg.lits_cap)
    (hagree : ∀ p < hdr.lits_len.toNat, lp.getD p 0#32 = litsPool.getD p 0#32)
    (hset : ∀ p < w, lp.getD (hdr.lits_len.toNat + p) 0#32 =
      litsPool.getD (a_off.toNat + p) 0#32 ^^^ 1#32)
    (ha_off_le : (sliceOffs.getD a 0#32).toNat + w ≤ hdr.lits_len.toNat)
    (hm_fin : (bytes progPtr progBytes ⋆ bvBlastMem cfg hdr1 atomBases
      (sliceOffs.set nodeIdx.toNat hdr.lits_len) aigWords htSlots lp ⋆ R) m')
    (hQ : BvEvalSubQ cfg progPtr progBytes vars cwords nodes prog hdr g atomBases nodeIdx R Q) :
    Q (true, ⟨⟩) m' := by
  subst hh1
  have haig1 := aigInv_set_litsLen (hdr.lits_len + BitVec.ofNat 32 w) haig
  have hok1 := bvWorkspaceOk_set_litsLen (hdr.lits_len + BitVec.ofNat 32 w) hok
  have hok2 := BVWorkspaceOk.set_litsPool hlp_len
    (BVWorkspaceOk.set_sliceOffs nodeIdx.toNat hdr.lits_len hok1)
  have hl_cap' := hinv.lits_le_cap
  refine hQ true _ g (sliceOffs.set nodeIdx.toNat hdr.lits_len) aigWords htSlots lp _
    hok2 haig1 (Aig.extends_rfl g) hinv.prog_ptr_eq rfl rfl
    (fun _ => ⟨hoom0, ?_⟩) hm_fin
  refine blastEvalInv_step hoom0 hinv hok2 haig1 (Aig.extends_rfl g) hni_lt hinv.prog_ptr_eq
    rfl rfl (by rw [hl1_len]; omega) (by rw [hl1_len]; omega) hagree ?_
  refine nodeDenotes_set_bv hnd_not (by rw [hl1_len]; omega) (fun k hk => ?_)
    (fun assign => ?_) (by rw [hok.so_len]; exact hni_lt)
  · rw [hset k hk, bv32_xor1_lsr1, ha_get]; exact ha_bd k hk
  · have hk' : hdr.lits_len.toNat + w ≤ lp.length := by rw [hlp_len]; omega
    rw [sliceDenotes_iff hk']; intro k hk
    rw [hset k hk, evalLit_xor1, bvExpr_not_getLsbD _ assign hk]
    have ha_sd_w := ha_sd assign
    have hl_ok : (sliceOffs.getD a 0#32).toNat + w ≤ litsPool.length := by
      rw [hok.lits_len]; omega
    rw [sliceDenotes_iff hl_ok] at ha_sd_w
    rw [ha_get, ha_sd_w k hk]

theorem drv0_getlsbd_lt_res {cfg : BVWorkspaceCfg} {progPtr : BitVec 64}
    {progBytes : List UInt8} {vars : BinTree VarEntry} {cwords : BinTree Nat}
    {nodes : BinTree ProgNode} {prog : BVLogicalExpr} {hdr : BVHdrState} {g : Aig}
    {ab so litsPool : List (BitVec 32)} {aw : List (BitVec 64)} {ht : List (BitVec 32)}
    {nodeIdx : BitVec 32} {a b ew : Nat} {ea : BVExpr ew}
    (hinv : BlastEvalInv cfg progPtr progBytes vars cwords nodes prog hdr g
      ab so aw ht litsPool nodeIdx.toNat)
    (hok : BVWorkspaceOk cfg hdr ab so aw ht litsPool) (hoom0 : hdr.oom = 0#32)
    (ha_lt : a < 4294967296) (hb_lt : b < 4294967296)
    (ha_lt_ni : a < nodeIdx.toNat) (hga : nodes.get? a = some (.bv ew ea))
    (hb_ew : b < ew) (ha_so : (BitVec.ofNat 32 a).toNat < so.length) :
    ∃ ha_b_lt : (so[(BitVec.ofNat 32 a).toNat]'ha_so + BitVec.ofNat 32 b).toNat < litsPool.length,
      (litsPool[(so[(BitVec.ofNat 32 a).toNat]'ha_so +
          BitVec.ofNat 32 b).toNat]'ha_b_lt >>> 1).toNat < g.A + 1 + g.nodes.size ∧
      ∀ assign : BVExpr.Assignment,
        g.evalLit (atomAssign progBytes assign) (UInt32.ofBitVec
            (litsPool[(so[(BitVec.ofNat 32 a).toNat]'ha_so + BitVec.ofNat 32 b).toNat]'ha_b_lt)) =
          (ea.eval assign).getLsbD b := by
  have hnda := hinv.prefix_ok hoom0 a ha_lt_ni
  unfold NodeDenotes at hnda; rw [hga] at hnda; dsimp only at hnda
  rcases hnda with ⟨ha_off_le, ha_bd, ha_sd⟩
  have ha_get : so[(BitVec.ofNat 32 a).toNat]'ha_so = so.getD a 0#32 := by
    rw [list_getD_eq_getElem, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]
  have ha_b_eq : (so[(BitVec.ofNat 32 a).toNat]'ha_so + BitVec.ofNat 32 b).toNat =
      (so[(BitVec.ofNat 32 a).toNat]'ha_so).toNat + b := by
    have := hinv.lits_le_cap; have := hok.lcap_lt
    rw [ha_get, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb_lt,
      Nat.mod_eq_of_lt (by omega : (so.getD a 0#32).toNat + b < 2 ^ 32)]
  have ha_b_lt :
      (so[(BitVec.ofNat 32 a).toNat]'ha_so + BitVec.ofNat 32 b).toNat < litsPool.length := by
    rw [hok.lits_len, ha_b_eq, ha_get]; have := hinv.lits_le_cap; omega
  refine ⟨ha_b_lt, ?_, fun assign => ?_⟩
  · rw [list_getD_eq_getElem, ha_b_eq, ha_get]; exact ha_bd b hb_ew
  · rw [list_getD_eq_getElem, ha_b_eq, ha_get]
    have ha_sd_w := ha_sd assign
    have hl_ok : (so.getD a 0#32).toNat + ew ≤ litsPool.length := by
      rw [hok.lits_len]; have := hinv.lits_le_cap; omega
    rw [sliceDenotes_iff hl_ok] at ha_sd_w; exact ha_sd_w b hb_ew

theorem drv0_node_width_read {progBytes : List UInt8} {vars : BinTree VarEntry}
    {cwords : BinTree Nat} {nodes : BinTree ProgNode} {prog : BVLogicalExpr}
    {cfg : BVWorkspaceCfg} {progPtr : BitVec 64} {hdr : BVHdrState} {g : Aig}
    {ab so : List (BitVec 32)} {aw : List (BitVec 64)} {ht lp : List (BitVec 32)}
    {nodeIdx : BitVec 32} {a : Nat}
    (hinv : BlastEvalInv cfg progPtr progBytes vars cwords nodes prog hdr g
      ab so aw ht lp nodeIdx.toNat)
    (hok : BVWorkspaceOk cfg hdr ab so aw ht lp) (ha_lt : a < 4294967296)
    (ha_lt_ni : a < nodeIdx.toNat) (hni_lt : nodeIdx.toNat < cfg.n_nodes) :
    (((8 : BitVec 64) + (hdr.n_vars.setWidth 64 <<< 1) + hdr.n_cwords.setWidth 64) +
        (BitVec.ofNat 32 a).setWidth 64 * 5 + 1).toNat =
      nodesOff cfg.n_vars hdr.n_cwords.toNat + 5 * a + 1 ∧
    4 * ((((8 : BitVec 64) + (hdr.n_vars.setWidth 64 <<< 1) + hdr.n_cwords.setWidth 64) +
        (BitVec.ofNat 32 a).setWidth 64 * 5 + 1).toNat + 1) ≤ progBytes.length := by
  have ha_nw := drv_node_word_ok hinv.parsed hinv.nv_eq hinv.nn_eq hinv.nc_eq hok.hdr_nv hok.nv_lt
    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]; omega :
      (BitVec.ofNat 32 a).toNat < cfg.n_nodes)
    1#64 1 rfl (by decide)
  have hew_idx : (((8 : BitVec 64) + (hdr.n_vars.setWidth 64 <<< 1) + hdr.n_cwords.setWidth 64) +
      (BitVec.ofNat 32 a).setWidth 64 * 5 + 1).toNat =
      nodesOff cfg.n_vars hdr.n_cwords.toNat + 5 * a + 1 := by
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] using ha_nw.1
  exact ⟨hew_idx, ha_nw.2⟩

theorem drv0_eq_lits_lt {progBytes : List UInt8} {cfg : BVWorkspaceCfg} {hdr hdr' : BVHdrState}
    {g g' : Aig} {ab so litsPool : List (BitVec 32)} {aw aw' : List (BitVec 64)}
    {ht ht' : List (BitVec 32)} {ew j a b : Nat} {ea eb : BVExpr ew}
    (hok : BVWorkspaceOk cfg hdr ab so aw ht litsPool) (hl_cap : hdr.lits_len.toNat ≤ cfg.lits_cap)
    (hext' : g ≤ g') (haig' : AigInv hdr' g' aw' ht')
    (ha_off_le : (so.getD a 0#32).toNat + ew ≤ hdr.lits_len.toNat)
    (hb_off_le : (so.getD b 0#32).toNat + ew ≤ hdr.lits_len.toNat)
    (ha_bd : ∀ k < ew, ((litsPool.getD ((so.getD a 0#32).toNat + k) 0#32) >>> 1).toNat <
      g.A + 1 + g.nodes.size)
    (hb_bd : ∀ k < ew, ((litsPool.getD ((so.getD b 0#32).toNat + k) 0#32) >>> 1).toNat <
      g.A + 1 + g.nodes.size)
    (ha_sd : ∀ assign : BVExpr.Assignment, SliceDenotes g (atomAssign progBytes assign)
      (litsSlice litsPool (so.getD a 0#32).toNat ew) (ea.eval assign))
    (hb_sd : ∀ assign : BVExpr.Assignment, SliceDenotes g (atomAssign progBytes assign)
      (litsSlice litsPool (so.getD b 0#32).toNat ew) (eb.eval assign))
    (ha_so : (BitVec.ofNat 32 a).toNat < so.length)
    (hb_so : (BitVec.ofNat 32 b).toNat < so.length)
    (ha_lt : a < 4294967296) (hb_lt : b < 4294967296) (hj_lt : j < ew) (hew_lt : ew < 2 ^ 32) :
    ∃ ha_j_lt : (so[(BitVec.ofNat 32 a).toNat]'ha_so + BitVec.ofNat 32 j).toNat < litsPool.length,
    ∃ hb_j_lt : (so[(BitVec.ofNat 32 b).toNat]'hb_so + BitVec.ofNat 32 j).toNat < litsPool.length,
      ((litsPool[(so[(BitVec.ofNat 32 a).toNat]'ha_so +
          BitVec.ofNat 32 j).toNat]'ha_j_lt) >>> 1).toNat < hdr'.aig_len.toNat ∧
      ((litsPool[(so[(BitVec.ofNat 32 b).toNat]'hb_so +
          BitVec.ofNat 32 j).toNat]'hb_j_lt) >>> 1).toNat < hdr'.aig_len.toNat ∧
      ∀ assign : BVExpr.Assignment,
        g'.evalLit (atomAssign progBytes assign) (UInt32.ofBitVec
            (litsPool[(so[(BitVec.ofNat 32 a).toNat]'ha_so + BitVec.ofNat 32 j).toNat]'ha_j_lt)) =
          (ea.eval assign).getLsbD j ∧
        g'.evalLit (atomAssign progBytes assign) (UInt32.ofBitVec
            (litsPool[(so[(BitVec.ofNat 32 b).toNat]'hb_so + BitVec.ofNat 32 j).toNat]'hb_j_lt)) =
          (eb.eval assign).getLsbD j := by
  have hj32 : j < 2 ^ 32 := Nat.lt_trans hj_lt hew_lt
  have hlcap_lt := hok.lcap_lt
  have ha_get : so[(BitVec.ofNat 32 a).toNat]'ha_so = so.getD a 0#32 := by
    rw [list_getD_eq_getElem, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]
  have hb_get : so[(BitVec.ofNat 32 b).toNat]'hb_so = so.getD b 0#32 := by
    rw [list_getD_eq_getElem, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb_lt]
  have ha_j_eq : (so[(BitVec.ofNat 32 a).toNat]'ha_so + BitVec.ofNat 32 j).toNat =
      (so.getD a 0#32).toNat + j := by
    rw [ha_get, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj32,
      Nat.mod_eq_of_lt (by omega : (so.getD a 0#32).toNat + j < 2 ^ 32)]
  have hb_j_eq : (so[(BitVec.ofNat 32 b).toNat]'hb_so + BitVec.ofNat 32 j).toNat =
      (so.getD b 0#32).toNat + j := by
    rw [hb_get, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj32,
      Nat.mod_eq_of_lt (by omega : (so.getD b 0#32).toNat + j < 2 ^ 32)]
  have ha_j_lt :
      (so[(BitVec.ofNat 32 a).toNat]'ha_so + BitVec.ofNat 32 j).toNat < litsPool.length := by
    rw [hok.lits_len, ha_j_eq]; omega
  have hb_j_lt :
      (so[(BitVec.ofNat 32 b).toNat]'hb_so + BitVec.ofNat 32 j).toNat < litsPool.length := by
    rw [hok.lits_len, hb_j_eq]; omega
  refine ⟨ha_j_lt, hb_j_lt, ?_, ?_, fun assign => ⟨?_, ?_⟩⟩
  · rw [haig'.aig_len_eq, list_getD_eq_getElem _ 0#32, ha_j_eq]
    have := hext'.1; have := hext'.2.1; have := ha_bd j hj_lt; omega
  · rw [haig'.aig_len_eq, list_getD_eq_getElem _ 0#32, hb_j_eq]
    have := hext'.1; have := hext'.2.1; have := hb_bd j hj_lt; omega
  · rw [Aig.evalLit_extend_node hext'
      (by rw [list_getD_eq_getElem _ 0#32, ha_j_eq]; exact ha_bd j hj_lt)]
    have ha_sd_w := ha_sd assign
    have hla_ok : (so.getD a 0#32).toNat + ew ≤ litsPool.length := by rw [hok.lits_len]; omega
    rw [sliceDenotes_iff hla_ok] at ha_sd_w
    rw [list_getD_eq_getElem _ 0#32, ha_j_eq]
    exact ha_sd_w j hj_lt
  · rw [Aig.evalLit_extend_node hext'
      (by rw [list_getD_eq_getElem _ 0#32, hb_j_eq]; exact hb_bd j hj_lt)]
    have hb_sd_w := hb_sd assign
    have hlb_ok : (so.getD b 0#32).toNat + ew ≤ litsPool.length := by rw [hok.lits_len]; omega
    rw [sliceDenotes_iff hlb_ok] at hb_sd_w
    rw [list_getD_eq_getElem _ 0#32, hb_j_eq]
    exact hb_sd_w j hj_lt

theorem drv0_eq_step_eval {progBytes : List UInt8} {hdr' hdr1 hdr2 : BVHdrState}
    {g' g1 g2 : Aig} {aw' : List (BitVec 64)} {ht' : List (BitVec 32)}
    {ew j : Nat} {ea eb : BVExpr ew} {acc acc' eqj la lb : BitVec 32}
    (hj_lt : j < ew) (hew_lt : ew < 2 ^ 32)
    (hext1 : g' ≤ g1) (haig' : AigInv hdr' g' aw' ht')
    (hacc_lt : (acc >>> 1).toNat < hdr'.aig_len.toNat)
    (hacc_ev : ∀ assign : BVExpr.Assignment,
      g'.evalLit (atomAssign progBytes assign) (UInt32.ofBitVec acc) =
        decide (∀ p < j, (ea.eval assign).getLsbD p = (eb.eval assign).getLsbD p))
    (hla_g' : ∀ assign : BVExpr.Assignment,
      g'.evalLit (atomAssign progBytes assign) (UInt32.ofBitVec la) = (ea.eval assign).getLsbD j)
    (hlb_g' : ∀ assign : BVExpr.Assignment,
      g'.evalLit (atomAssign progBytes assign) (UInt32.ofBitVec lb) = (eb.eval assign).getLsbD j)
    (hoom_pr2 : hdr1.oom ≠ 0#32 → hdr2.oom ≠ 0#32)
    (hoom2 : hdr2.oom = 0#32)
    (heq_res : hdr1.oom = 0#32 → (eqj >>> 1).toNat < hdr1.aig_len.toNat ∧
      ∀ ρ : Nat → Bool, g1.evalLit ρ (UInt32.ofBitVec eqj) =
        (g'.evalLit ρ (UInt32.ofBitVec la) == g'.evalLit ρ (UInt32.ofBitVec lb)))
    (hand_res : hdr2.oom = 0#32 → (acc' >>> 1).toNat < hdr2.aig_len.toNat ∧
      ∀ ρ : Nat → Bool, g2.evalLit ρ (UInt32.ofBitVec acc') =
        (g1.evalLit ρ (UInt32.ofBitVec acc) && g1.evalLit ρ (UInt32.ofBitVec eqj))) :
    BitVec.ofNat 32 j + 1 = BitVec.ofNat 32 (j + 1) ∧
    (acc' >>> 1).toNat < hdr2.aig_len.toNat ∧
    ∀ assign : BVExpr.Assignment,
      g2.evalLit (atomAssign progBytes assign) (UInt32.ofBitVec acc') =
        decide (∀ p < j + 1, (ea.eval assign).getLsbD p = (eb.eval assign).getLsbD p) := by
  have hj32 : j < 2 ^ 32 := Nat.lt_trans hj_lt hew_lt
  have hj_eq32 : BitVec.ofNat 32 j + 1 = BitVec.ofNat 32 (j + 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl,
      Nat.mod_eq_of_lt hj32, Nat.mod_eq_of_lt (by omega : j + 1 < 2 ^ 32)]
  have hoom1 : hdr1.oom = 0#32 := Classical.byContradiction fun hne => hoom_pr2 hne hoom2
  have heq_ok := heq_res hoom1
  have hand_ok := hand_res hoom2
  refine ⟨hj_eq32, hand_ok.1, fun assign => ?_⟩
  have hacc_g1 : g1.evalLit (atomAssign progBytes assign) (UInt32.ofBitVec acc) =
      decide (∀ p < j, (ea.eval assign).getLsbD p = (eb.eval assign).getLsbD p) := by
    rw [Aig.evalLit_extend_node hext1 (by rw [haig'.aig_len_eq] at hacc_lt; exact hacc_lt)]
    exact hacc_ev assign
  have heqj_g1 : g1.evalLit (atomAssign progBytes assign) (UInt32.ofBitVec eqj) =
      ((ea.eval assign).getLsbD j == (eb.eval assign).getLsbD j) := by
    have hraw := heq_ok.2 (atomAssign progBytes assign)
    change g1.evalLit (atomAssign progBytes assign) (UInt32.ofBitVec eqj) =
      (g'.evalLit (atomAssign progBytes assign) (UInt32.ofBitVec la) ==
        g'.evalLit (atomAssign progBytes assign) (UInt32.ofBitVec lb)) at hraw
    rw [hraw, hla_g' assign, hlb_g' assign]
  rw [hand_ok.2 (atomAssign progBytes assign), hacc_g1, heqj_g1]
  by_cases h1 : ∀ p < j, (ea.eval assign).getLsbD p = (eb.eval assign).getLsbD p <;>
    by_cases h2 : (ea.eval assign).getLsbD j = (eb.eval assign).getLsbD j
  · rw [decide_eq_true h1,
      show ((ea.eval assign).getLsbD j == (eb.eval assign).getLsbD j) = true from beq_iff_eq.mpr h2]
    rw [Bool.and_true, eq_comm, decide_eq_true_eq]
    intro p hp
    by_cases hpj : p = j
    · subst hpj; exact h2
    · exact h1 p (by omega)
  · rw [decide_eq_true h1,
      show ((ea.eval assign).getLsbD j == (eb.eval assign).getLsbD j) = false from by simp [h2]]
    rw [Bool.and_false, eq_comm, decide_eq_false_iff_not]
    exact fun h => h2 (h j (by omega))
  · rw [decide_eq_false h1]; rw [Bool.false_and, eq_comm, decide_eq_false_iff_not]
    exact fun h => h1 (fun p hp => h p (by omega))
  · rw [decide_eq_false h1]; rw [Bool.false_and, eq_comm, decide_eq_false_iff_not]
    exact fun h => h1 (fun p hp => h p (by omega))

theorem drv0_eq_post {cfg : BVWorkspaceCfg} {progPtr : BitVec 64} {progBytes : List UInt8}
    {vars : BinTree VarEntry} {cwords : BinTree Nat} {nodes : BinTree ProgNode}
    {prog : BVLogicalExpr} {hdr hdr' : BVHdrState} {g g' : Aig}
    {atomBases sliceOffs : List (BitVec 32)} {aigWords aw' : List (BitVec 64)}
    {htSlots hts' litsPool : List (BitVec 32)} {nodeIdx acc : BitVec 32}
    {ew : Nat} {ea eb : BVExpr ew} {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post [.bool]}
    (hoom0 : hdr.oom = 0#32) (hoom' : hdr'.oom = 0#32) (hni_lt : nodeIdx.toNat < cfg.n_nodes)
    (hok : BVWorkspaceOk cfg hdr atomBases sliceOffs aigWords htSlots litsPool)
    (hok' : BVWorkspaceOk cfg hdr' atomBases sliceOffs aw' hts' litsPool)
    (haig' : AigInv hdr' g' aw' hts') (hext' : g ≤ g')
    (hinv : BlastEvalInv cfg progPtr progBytes vars cwords nodes prog hdr g
      atomBases sliceOffs aigWords htSlots litsPool nodeIdx.toNat)
    (hpp' : hdr'.prog_ptr = progPtr) (hnc' : hdr'.n_cwords = hdr.n_cwords)
    (hrt' : hdr'.root_node = hdr.root_node) (hlits' : hdr'.lits_len = hdr.lits_len)
    (hacc_lt : (acc >>> 1).toNat < hdr'.aig_len.toNat)
    (hacc_ev : ∀ assign : BVExpr.Assignment,
      g'.evalLit (atomAssign progBytes assign) (UInt32.ofBitVec acc) =
        decide (∀ p < ew, (ea.eval assign).getLsbD p = (eb.eval assign).getLsbD p))
    (hnd_eq : nodes.get? nodeIdx.toNat = some (.bool (.literal (.bin ea .eq eb))))
    (hm_so : (array (t := i32) hdr.slice_off_ptr (sliceOffs.set nodeIdx.toNat acc) ⋆
      blastSoRest cfg hdr' progPtr progBytes atomBases aw' hts' litsPool R) m')
    (hQ : BvEvalSubQ cfg progPtr progBytes vars cwords nodes prog hdr g atomBases nodeIdx R Q) :
    Q (true, ⟨⟩) m' := by
  have hso_ptr : hdr'.slice_off_ptr = hdr.slice_off_ptr := hok'.hdr_so.trans hok.hdr_so.symm
  have hok2 := BVWorkspaceOk.set_sliceOffs nodeIdx.toNat acc hok'
  refine hQ true hdr' g' (sliceOffs.set nodeIdx.toNat acc) aw' hts' litsPool _ hok2 haig'
    hext' hpp' hnc' hrt' (fun _ => ⟨hoom', ?_⟩)
    (blast_so_unfocus hok'.hdr_so (by rw [hso_ptr]; exact hm_so))
  refine blastEvalInv_step hoom0 hinv hok2 haig' hext' hni_lt hpp' hnc' hrt'
    (by rw [hlits']; exact Nat.le_refl _) (by rw [hlits']; exact hinv.lits_le_cap)
    (fun _ _ => rfl) ?_
  refine nodeDenotes_set_bool hnd_eq (by rw [← haig'.aig_len_eq]; exact hacc_lt)
    (fun assign => ?_) (by rw [hok.so_len]; exact hni_lt)
  rw [bvLogical_lit_eq_eval, hacc_ev assign]

theorem blast_hdr_left {cfg : BVWorkspaceCfg} {hdr : BVHdrState}
    {progPtr : BitVec 64} {progBytes : List UInt8}
    {atomBases sliceOffs : List (BitVec 32)} {aigWords : List (BitVec 64)}
    {htSlots litsPool : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (bytes progPtr progBytes ⋆
      bvBlastMem cfg hdr atomBases sliceOffs aigWords htSlots litsPool ⋆ R) m) :
    (bvHdrMem cfg.work_base hdr ⋆ (bytes progPtr progBytes ⋆
      (array (t := i32) (cfg.work_base + 128) atomBases ⋆
      region (cfg.work_base + BitVec.ofNat 64 (128 + 4 * cfg.n_vars))
        (cfg.atom_bytes - 4 * cfg.n_vars) ⋆
      array (t := i32) (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes)) sliceOffs ⋆
      region (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes + 4 * cfg.n_nodes))
        (cfg.slice_bytes - 4 * cfg.n_nodes) ⋆
      array64 cfg.aig_ptr aigWords ⋆ array (t := i32) cfg.ht_ptr htSlots ⋆
      array (t := i32) cfg.lits_ptr litsPool ⋆
      region (cfg.lits_ptr + BitVec.ofNat 64 (4 * cfg.lits_cap))
        (cfg.lits_bytes - 4 * cfg.lits_cap) ⋆ R))) m := by
  rw [bvBlastMem_hdr_left] at hm; exact sep_ac hm

theorem blast_ab_focus {cfg : BVWorkspaceCfg} {hdr : BVHdrState}
    {progPtr : BitVec 64} {progBytes : List UInt8}
    {atomBases sliceOffs : List (BitVec 32)} {aigWords : List (BitVec 64)}
    {htSlots litsPool : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (hab : hdr.atom_base_ptr = cfg.work_base + 128)
    (hm : (bytes progPtr progBytes ⋆
      bvBlastMem cfg hdr atomBases sliceOffs aigWords htSlots litsPool ⋆ R) m) :
    (array (t := i32) hdr.atom_base_ptr atomBases ⋆
      (bvHdrMem cfg.work_base hdr ⋆ bytes progPtr progBytes ⋆
      region (cfg.work_base + BitVec.ofNat 64 (128 + 4 * cfg.n_vars))
        (cfg.atom_bytes - 4 * cfg.n_vars) ⋆
      array (t := i32) (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes)) sliceOffs ⋆
      region (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes + 4 * cfg.n_nodes))
        (cfg.slice_bytes - 4 * cfg.n_nodes) ⋆
      array64 cfg.aig_ptr aigWords ⋆ array (t := i32) cfg.ht_ptr htSlots ⋆
      array (t := i32) cfg.lits_ptr litsPool ⋆
      region (cfg.lits_ptr + BitVec.ofNat 64 (4 * cfg.lits_cap))
        (cfg.lits_bytes - 4 * cfg.lits_cap) ⋆ R)) m := by
  rw [bvBlastMem_ab_focus] at hm; rw [hab]; exact sep_ac hm

theorem drv0_loop_lt {j w : Nat} (hle : j ≤ w) (hw : w < 2 ^ 32)
    (hc : j % 2 ^ 32 < w % 2 ^ 32) : j < w := by
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hle hw), Nat.mod_eq_of_lt hw] at hc; exact hc

theorem drv0_loop_eq {j w : Nat} (hle : j ≤ w) (hw : w < 2 ^ 32)
    (hc : ¬ j % 2 ^ 32 < w % 2 ^ 32) : j = w := by
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hle hw), Nat.mod_eq_of_lt hw] at hc
  exact Nat.le_antisymm hle (Nat.le_of_not_lt hc)

theorem drv0_lt_of_mod {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32)
    (hc : a % 2 ^ 32 < b % 2 ^ 32) : a < b := by
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hc

theorem drv0_le_of_not_mod {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32)
    (hc : ¬ a % 2 ^ 32 < b % 2 ^ 32) : b ≤ a := by
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hc; exact Nat.le_of_not_lt hc

theorem drv0_oom_close {cfg : BVWorkspaceCfg} {progPtr : BitVec 64} {progBytes : List UInt8}
    {vars : BinTree VarEntry} {cwords : BinTree Nat} {nodes : BinTree ProgNode}
    {prog : BVLogicalExpr} {hdr : BVHdrState} {g : Aig}
    {atomBases sliceOffs : List (BitVec 32)} {aigWords : List (BitVec 64)}
    {htSlots litsPool : List (BitVec 32)} {nodeIdx : BitVec 32}
    {R : Mem 64 → Prop} {m1 : Mem 64} {Q : Post [.bool]}
    (hok : BVWorkspaceOk cfg hdr atomBases sliceOffs aigWords htSlots litsPool)
    (haig : AigInv hdr g aigWords htSlots)
    (hinv : BlastEvalInv cfg progPtr progBytes vars cwords nodes prog hdr g
      atomBases sliceOffs aigWords htSlots litsPool nodeIdx.toNat)
    (hm1 : (bytes progPtr progBytes ⋆
      bvBlastMem cfg { hdr with oom := 1#32 } atomBases sliceOffs aigWords htSlots litsPool ⋆
        R) m1)
    (hQ : BvEvalSubQ cfg progPtr progBytes vars cwords nodes prog hdr g atomBases nodeIdx R Q) :
    Q (false, ⟨⟩) m1 :=
  hQ false { hdr with oom := 1#32 } g sliceOffs aigWords htSlots litsPool m1
    (bvWorkspaceOk_set_oom 1#32 hok) (aigInv_set_oom 1#32 haig) (Aig.extends_rfl g)
    hinv.prog_ptr_eq rfl rfl (fun hf => absurd hf Bool.false_ne_true) hm1

theorem drv0_eq_frame {cfg : BVWorkspaceCfg} {progPtr : BitVec 64}
    {hdr hdr' hdr1 hdr2 : BVHdrState} {g g' g1 g2 : Aig}
    {atomBases sliceOffs litsPool : List (BitVec 32)}
    {aw' aw1 aw2 : List (BitVec 64)} {hts' hts1 hts2 : List (BitVec 32)}
    (hext' : g ≤ g') (hext1 : g' ≤ g1) (hext2 : g1 ≤ g2)
    (hpp' : hdr'.prog_ptr = progPtr) (hnc' : hdr'.n_cwords = hdr.n_cwords)
    (hrt' : hdr'.root_node = hdr.root_node) (hlits' : hdr'.lits_len = hdr.lits_len)
    (hfr1 : hdr'.AigFrame hdr1) (hfr2 : hdr1.AigFrame hdr2)
    (hok' : BVWorkspaceOk cfg hdr' atomBases sliceOffs aw' hts' litsPool)
    (haig1 : AigInv hdr1 g1 aw1 hts1) (haig2 : AigInv hdr2 g2 aw2 hts2) :
    BVWorkspaceOk cfg hdr2 atomBases sliceOffs aw2 hts2 litsPool ∧ g ≤ g2 ∧
    hdr2.prog_ptr = progPtr ∧ hdr2.n_cwords = hdr.n_cwords ∧
    hdr2.root_node = hdr.root_node ∧ hdr2.lits_len = hdr.lits_len :=
  ⟨bvWorkspaceOk_of_aigFrame (bvWorkspaceOk_of_aigFrame hok' hfr1 haig1) hfr2 haig2,
    Aig.extends_trans hext' (Aig.extends_trans hext1 hext2),
    hfr2.prog_ptr.trans (hfr1.prog_ptr.trans hpp'),
    hfr2.n_cwords.trans (hfr1.n_cwords.trans hnc'),
    hfr2.root_node.trans (hfr1.root_node.trans hrt'),
    hfr2.lits_len.trans (hfr1.lits_len.trans hlits')⟩

end

end LeanQbe.T.Examples.Bitblast.Proof
