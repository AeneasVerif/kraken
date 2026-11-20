module

public import LeanQbe.T.Examples.Kissat.FullBveVarLemmas2
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` UNSAT-Only BVE Top-Shard Proofs — Hub (`Stage 4`, BVE-Var)

Re-exports `full_bve_ext_need_wp`, `full_bve_commit_res_wp` (`FullBveVarLemmas2`), and provides
the parametric `(Γ : Env)` `Func.wp` proof for `full_bve_var` (`full_bve_var_wp`), matching
`FullSpec3.fullBveVarSpec` (`FullBveVarSpecs.fullBveVarSpec`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

open FullBveVarTactics FullBveVarSpecs FullBveVarHelpers

section
open FullArenaTactics
open scoped FullArenaTactics FullBveVarTactics

/-! ## 1. Depth-free local `wp` stepping combinators (zero recursion into `Expr` lambdas) -/

private theorem bl_fst {α β : Type _} (a : α) (b : β) : (a, b).fst = a := rfl
private theorem bl_snd {α β : Type _} (a : α) (b : β) : (a, b).snd = b := rfl
private theorem bl_add32 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i32} {k m} :
    wp Γ Q X (.let_ (Op.mk (.add i32) (a, b, ())) k) m =
      wp Γ Q X (k (a.val + b.val, ())) m := by simp [wp_let_add_eq, lift2]
private theorem bl_add64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i64} {k m} :
    wp Γ Q X (.let_ (Op.mk (.add i64) (a, b, ())) k) m =
      wp Γ Q X (k (a.val + b.val, ())) m := by simp [wp_let_add_eq, lift2]
private theorem bl_sub64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i64} {k m} :
    wp Γ Q X (.let_ (Op.mk (.sub i64) (a, b, ())) k) m =
      wp Γ Q X (k (a.val - b.val, ())) m := by simp [wp_let_sub_eq, lift2]
private theorem bl_mul64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i64} {k m} :
    wp Γ Q X (.let_ (Op.mk (.mul i64) (a, b, ())) k) m =
      wp Γ Q X (k (a.val * b.val, ())) m := by simp [wp_let_mul_eq, lift2]
private theorem bl_shl32 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i32} {k m} :
    wp Γ Q X (.let_ (Op.mk (.shl i32) (a, b, ())) k) m =
      wp Γ Q X (k (a.val <<< (b.val.toNat % 32), ())) m := by simp [wp_let_shl_eq, lift2]
private theorem bl_shl64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i64} {k m} :
    wp Γ Q X (.let_ (Op.mk (.shl i64) (a, b, ())) k) m =
      wp Γ Q X (k (a.val <<< (b.val.toNat % 64), ())) m := by simp [wp_let_shl_eq, lift2]
private theorem bl_lshr64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i64} {k m} :
    wp Γ Q X (.let_ (Op.mk (.lshr i64) (a, b, ())) k) m =
      wp Γ Q X (k (a.val >>> (b.val.toNat % 64), ())) m := by simp [wp_let_lshr_eq, lift2]
private theorem bl_and32 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i32} {k m} :
    wp Γ Q X (.let_ (Op.mk (.and i32) (a, b, ())) k) m =
      wp Γ Q X (k (a.val &&& b.val, ())) m := by simp [wp_let_and_eq, lift2]
private theorem bl_and64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i64} {k m} :
    wp Γ Q X (.let_ (Op.mk (.and i64) (a, b, ())) k) m =
      wp Γ Q X (k (a.val &&& b.val, ())) m := by simp [wp_let_and_eq, lift2]
private theorem bl_or32 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i32} {k m} :
    wp Γ Q X (.let_ (Op.mk (.or i32) (a, b, ())) k) m =
      wp Γ Q X (k (a.val ||| b.val, ())) m := by simp [wp_let_or_eq, lift2]
private theorem bl_or64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i64} {k m} :
    wp Γ Q X (.let_ (Op.mk (.or i64) (a, b, ())) k) m =
      wp Γ Q X (k (a.val ||| b.val, ())) m := by simp [wp_let_or_eq, lift2]
private theorem bl_zext32_64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a : Arg Val i32} {k m} :
    wp Γ Q X (.let_ (Op.mk (.zext 32 64) (a, ())) k) m =
      wp Γ Q X (k (a.val.setWidth 64, ())) m := by simp [wp_let_zext_eq]
private theorem bl_sext32_64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a : Arg Val i32} {k m} :
    wp Γ Q X (.let_ (Op.mk (.sext 32 64) (a, ())) k) m =
      wp Γ Q X (k (a.val.signExtend 64, ())) m := by simp [wp_let_sext_eq]
private theorem bl_trunc64_32 {Γ} {rs : List Ty} {Q : Post rs} {X} {a : Arg Val i64} {k m} :
    wp Γ Q X (.let_ (Op.mk (.trunc 64 32) (a, ())) k) m =
      wp Γ Q X (k (a.val.setWidth 32, ())) m := by simp [wp_let_trunc_eq]
private theorem bl_ult32 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i32} {h} {k m} :
    wp Γ Q X (.let_ (Op.mk (.cmp .ult i32 .bool h) (a, b, ())) k) m =
      wp Γ Q X (k (a.val.ult b.val, ())) m := by simp [wp_let_cmp_eq, liftCmp, evalBits_ult_eq]
private theorem bl_ugt32 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i32} {h} {k m} :
    wp Γ Q X (.let_ (Op.mk (.cmp .ugt i32 .bool h) (a, b, ())) k) m =
      wp Γ Q X (k (b.val.ult a.val, ())) m := by simp [wp_let_cmp_eq, liftCmp, evalBits_ugt_eq]
private theorem bl_ult64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i64} {h} {k m} :
    wp Γ Q X (.let_ (Op.mk (.cmp .ult i64 .bool h) (a, b, ())) k) m =
      wp Γ Q X (k (a.val.ult b.val, ())) m := by simp [wp_let_cmp_eq, liftCmp, evalBits_ult_eq]
private theorem bl_ule64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i64} {h} {k m} :
    wp Γ Q X (.let_ (Op.mk (.cmp .ule i64 .bool h) (a, b, ())) k) m =
      wp Γ Q X (k (a.val.ule b.val, ())) m := by simp [wp_let_cmp_eq, liftCmp, evalBits_ule_eq]
private theorem bl_ugt64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i64} {h} {k m} :
    wp Γ Q X (.let_ (Op.mk (.cmp .ugt i64 .bool h) (a, b, ())) k) m =
      wp Γ Q X (k (b.val.ult a.val, ())) m := by simp [wp_let_cmp_eq, liftCmp, evalBits_ugt_eq]
private theorem bl_eq32 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i32} {h} {k m} :
    wp Γ Q X (.let_ (Op.mk (.cmp .eq i32 .bool h) (a, b, ())) k) m =
      wp Γ Q X (k (a.val == b.val, ())) m := by simp [wp_let_cmp_eq, liftCmp, evalBits_eq_beq]
private theorem bl_ne32 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i32} {h} {k m} :
    wp Γ Q X (.let_ (Op.mk (.cmp .ne i32 .bool h) (a, b, ())) k) m =
      wp Γ Q X (k (a.val != b.val, ())) m := by simp [wp_let_cmp_eq, liftCmp, evalBits_ne_bne]
private theorem bl_eq64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i64} {h} {k m} :
    wp Γ Q X (.let_ (Op.mk (.cmp .eq i64 .bool h) (a, b, ())) k) m =
      wp Γ Q X (k (a.val == b.val, ())) m := by simp [wp_let_cmp_eq, liftCmp, evalBits_eq_beq]
private theorem bl_copy_bool {Γ} {rs : List Ty} {Q : Post rs} {X} {a : Arg Val .bool} {k m} :
    wp Γ Q X (.let_ (Op.mk (.copy .bool) (a, ())) k) m =
      wp Γ Q X (k (a.val, ())) m := by simp [wp_let_copy_eq]
private theorem bl_copy32 {Γ} {rs : List Ty} {Q : Post rs} {X} {a : Arg Val i32} {k m} :
    wp Γ Q X (.let_ (Op.mk (.copy i32) (a, ())) k) m =
      wp Γ Q X (k (a.val, ())) m := by simp [wp_let_copy_eq]
private theorem bl_copy64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a : Arg Val i64} {k m} :
    wp Γ Q X (.let_ (Op.mk (.copy i64) (a, ())) k) m =
      wp Γ Q X (k (a.val, ())) m := by simp [wp_let_copy_eq]
private theorem bl_ret {Γ} {rs : List Ty} {Q : Post rs} {X} {args : Tup (Arg Val) rs} {m} :
    wp Γ Q X (.ret args) m = Q (LeanQbe.T.vals args) m := rfl
private theorem bl_jump {Γ} {rs ts : List Ty} {Q : Post rs} {X} {L : Cont ts}
    {args : Tup (Arg Val) ts} {m} : wp Γ Q X (.jump L args) m = L (LeanQbe.T.vals args) m := rfl
private theorem bl_jnz {Γ} {rs : List Ty} {Q : Post rs} {X} {c : Val .bool} {t e m} :
    wp Γ Q X (.jnz (.var c) t e) m =
      ((c = true → wp Γ Q X t m) ∧ (c = false → wp Γ Q X e m)) := rfl

private theorem bl_wp_beta {Γ : Env} {rs bs : List Ty} {Q : Post rs} {X : XPost}
    {k : Tup Val bs → Expr Val Cont rs} {r : Tup Val bs} {m' : Mem 64} :
    (fun r0 m0 => wp Γ Q X (k r0) m0) r m' = wp Γ Q X (k r) m' := rfl

local syntax "bve_lets" : tactic
local macro_rules
  | `(tactic| bve_lets) => `(tactic| (
      (try rw [bl_wp_beta]);
      repeat (first
        | rw [bl_fst] | rw [bl_snd]
        | rw [bl_add32] | rw [bl_add64] | rw [bl_sub64] | rw [bl_mul64]
        | rw [bl_shl32] | rw [bl_shl64] | rw [bl_lshr64]
        | rw [bl_and32] | rw [bl_and64] | rw [bl_or32] | rw [bl_or64]
        | rw [bl_zext32_64] | rw [bl_sext32_64] | rw [bl_trunc64_32]
        | rw [bl_ult32] | rw [bl_ugt32] | rw [bl_ult64] | rw [bl_ule64] | rw [bl_ugt64]
        | rw [bl_eq32] | rw [bl_ne32] | rw [bl_eq64]
        | rw [bl_copy_bool] | rw [bl_copy32] | rw [bl_copy64]
        | rw [Arg.val_var] | rw [Arg.val_imm])))

local macro "bve_ld " lem:term : tactic =>
  `(tactic| (bve_lets; refine wp_load_of $lem ?_; bve_lets))

local macro "bve_st " m:ident ", " h:ident " := " lem:term : tactic =>
  `(tactic| ((bve_lets; apply wp_store_sep; · exact $lem); intro $m:ident $h:ident; bve_lets))

local macro "bve_jnz " hc:ident : tactic =>
  `(tactic| (bve_lets; rw [bl_jnz]; refine ⟨fun $hc:ident => ?_, fun $hc:ident => ?_⟩))

local macro "bve_ret" : tactic =>
  `(tactic| (bve_lets; rw [bl_ret]; simp only [vals_nil, vals_cons, Arg.val_var, Arg.val_imm]))

local macro "bve_jump" : tactic =>
  `(tactic| (bve_lets; rw [bl_jump]; simp only [vals_nil, vals_cons, Arg.val_var, Arg.val_imm]))

/-! ## 2. Main `Func.wp` Proof: `full_bve_var` -/

/-- Parametric `(Γ : Env)` `Func.wp` proof for `full_bve_var` (`Stage 4` UNSAT-only). -/
theorem full_bve_var_wp (Γ : Env)
    (hCollect : ∀ xs m Q X, fullBveCollectSpec xs m Q X →
      Γ "full_bve_collect" [i64, i32, i64, i32] [i32] xs m Q X)
    (hExtNeed : ∀ xs m Q X, fullBveExtNeedSpec xs m Q X →
      Γ "full_bve_ext_need" [i64, i32, i32] [i64] xs m Q X)
    (hWeaken : ∀ xs m Q X, fullBveWeakenSpec xs m Q X →
      Γ "full_bve_weaken" [i64, i32, i32, i32] [.bool] xs m Q X)
    (hSetInact : ∀ xs m Q X, fullSetInactiveSpec xs m Q X →
      Γ "full_set_inactive" [i64, i32, i32] [] xs m Q X)
    (hGates : ∀ xs m Q X, fullBveGatesSpec xs m Q X →
      Γ "full_bve_gates" [i64, i32, i32, i32] [] xs m Q X)
    (hResolve : ∀ xs m Q X, fullBveResolvePairSpec xs m Q X →
      Γ "full_bve_resolve_pair" [i64, i32, i32, i32] [.bool] xs m Q X)
    (hCommitRes : ∀ xs m Q X, fullBveCommitResSpec xs m Q X →
      Γ "full_bve_commit_res" [i64, i64, i64] [i64] xs m Q X)
    (hTryBce : ∀ xs m Q X, fullBveTryBceSpec xs m Q X →
      Γ "full_bve_try_bce" [i64, i32, i32, i32, i32] [.bool] xs m Q X)
    (hExtPush2 : ∀ xs m Q X, fullExtendPush2Spec xs m Q X →
      Γ "full_extend_push2" [i64, i32, i32] [.bool] xs m Q X)
    (hDelBin : ∀ xs m Q X, fullDeleteBinarySpec xs m Q X →
      Γ "full_delete_binary" [i64, i32, i32] [] xs m Q X)
    (hExtPushCl : ∀ xs m Q X, fullExtendPushClSpec xs m Q X →
      Γ "full_extend_push_cl" [i64, i32, i32] [.bool] xs m Q X) :
    ∀ args m Q X, fullBveVarSpec args m Q X → Func.wp Γ full_bve_var_body args m Q X := by
  rintro ⟨h, v, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hdense, hv_lt, hm, hQ⟩
  obtain ⟨F_cur, hinv⟩ := fullDenseInv_exists_witness hdense
  have hmv := c.hmaxv; have harc := c.harena; have hsc := c.hscr
  unfold dimacsBound at hmv harc hsc
  have hcv_le : s.core.cur_vars ≤ c.max_vars := hinv.1.core_ok.cur_vars_le
  have hv_lt32 : 2 * v.toNat < 2 ^ 32 := by omega
  let pl := v <<< ((1 : BitVec 32).toNat % 32)
  have hpl_nat : pl.toNat = 2 * v.toNat := by
    dsimp only [pl]; exact bv32_shl1_toNat hv_lt32
  have hnl_nat : (pl ||| 1#32).toNat = 2 * v.toNat + 1 := bv32_or1_even_toNat hpl_nat
  unfold Func.wp full_bve_var_body
  bve_ld load_full_scratch_cap hm
  bve_jnz hsc_ult
  · -- scratch_cap < 512 -> return 1
    bve_ret
    exact hQ 1#64 s m hdense (Nat.le_refl _) (Nat.le_refl _) (Or.inl rfl)
      (fun h => by cases h) hm
  · -- scratch_cap >= 512 -> full_bve_collect(pl), full_bve_collect(nl)
    have hsc512 : 512 ≤ c.scratch_cap := by
      rw [BitVec.ult, decide_eq_false_iff_not, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : c.scratch_cap < 2 ^ 64),
        show (512 : BitVec 64).toNat = 512 from rfl] at hsc_ult
      omega
    bve_ld load_full_scratch_buf_ptr hm
    bve_lets
    refine wp_call_of_spec _ _ (hCollect _ _ _ X ?_)
    simp only [vals_nil, vals_cons, Arg.val_var, Arg.val_imm]
    refine ⟨c, F0, F_cur, s, 0, R, rfl, hinv,
      (by change pl.toNat < 2 * s.core.cur_vars; rw [hpl_nat]; omega),
      (by rw [Nat.mul_zero]; exact (BitVec.add_zero c.pScratchBuf).symm),
      (by rw [show (32 : BitVec 32).toNat = 32 from rfl]; omega), hm, ?_⟩
    dsimp only
    rintro np scr1 m1 hlen1 hkeep1 hres1 hm1
    let s1 : FullState := { s with scratch := { s.scratch with scratch_buf := scr1 } }
    have hinv1 := FullDenseInvW.with_scratch_buf hinv hlen1
    have hptr64 : c.pScratchBuf + (BitVec.signExtend 64 64#32) * 4 =
        c.pScratchBuf + BitVec.ofNat 64 (4 * 64) := by
      apply congrArg (c.pScratchBuf + ·); decide
    bve_lets
    refine wp_call_of_spec _ _ (hCollect _ _ _ X ?_)
    simp only [vals_nil, vals_cons, Arg.val_var, Arg.val_imm]
    refine ⟨c, F0, F_cur, s1, 64, R, rfl, hinv1,
      (by change (pl ||| 1#32).toNat < 2 * s.core.cur_vars; rw [hnl_nat]; omega),
      hptr64, (by rw [show (32 : BitVec 32).toNat = 32 from rfl]; omega), hm1, ?_⟩
    dsimp only
    rintro nn scr2 m2 hlen2 hkeep2 hres2 hm2
    let s2 : FullState := { s1 with scratch := { s1.scratch with scratch_buf := scr2 } }
    have hinv2 := FullDenseInvW.with_scratch_buf hinv1 hlen2
    bve_jnz hnp_eq
    · -- np == 0xFFFFFFFF -> return 1
      bve_ret
      exact hQ 1#64 s2 m2 hinv2.toDense (Nat.le_refl _) (Nat.le_refl _) (Or.inl rfl)
        (fun h => by cases h) hm2
    · bve_jnz hnn_eq
      · -- nn == 0xFFFFFFFF -> return 1
        bve_ret
        exact hQ 1#64 s2 m2 hinv2.toDense (Nat.le_refl _) (Nat.le_refl _) (Or.inl rfl)
          (fun h => by cases h) hm2
      · -- np <= 32, nn <= 32
        have hnp_ne : np ≠ 0xFFFFFFFF#32 := by
          intro h; rw [h] at hnp_eq; cases hnp_eq
        have hnn_ne : nn ≠ 0xFFFFFFFF#32 := by
          intro h; rw [h] at hnn_eq; cases hnn_eq
        have hnp_res : np.toNat ≤ 32 ∧
            ∀ i < np.toNat, FullBveEntryOkW F_cur s1 pl.toNat (scr1[i]?.getD 0#32) := by
          rcases hres1 with rfl | h
          · exact absurd rfl hnp_ne
          · exact ⟨by simpa only [show (32 : BitVec 32).toNat = 32 from rfl] using h.1,
              fun i hi => by simpa only [Nat.zero_add] using h.2 i hi⟩
        have hnn_res : nn.toNat ≤ 32 ∧
            ∀ j < nn.toNat, FullBveEntryOkW F_cur s2 (pl ||| 1#32).toNat
              (scr2[64 + j]?.getD 0#32) := by
          rcases hres2 with rfl | h
          · exact absurd rfl hnn_ne
          · exact ⟨by simpa only [show (32 : BitVec 32).toNat = 32 from rfl] using h.1, h.2⟩
        have hnp_le : np.toNat ≤ 32 := hnp_res.1
        have hnn_le : nn.toNat ≤ 32 := hnn_res.1
        have hp_ok : ∀ i < np.toNat,
            FullBveEntryOkW F_cur s2 (2 * v.toNat) (scr2[i]?.getD 0#32) := fun i hi => by
          rw [hkeep2 i (by omega) (Or.inl (by omega)), ← hpl_nat]
          exact FullBveEntryOkW.with_state (Nat.le_refl _) rfl rfl (hnp_res.2 i hi)
        have hn_ok : ∀ j < nn.toNat,
            FullBveEntryOkW F_cur s2 (2 * v.toNat + 1) (scr2[64 + j]?.getD 0#32) :=
          fun j hj => by rw [← hnl_nat]; exact hnn_res.2 j hj
        have hs2_cv : s2.core.cur_vars = s.core.cur_vars := rfl
        have hs2_fl : s2.core.fuel = s.core.fuel := rfl
        have h0_32 : (0 : BitVec 32).toNat = 0 := rfl
        have h64_32 : (64 : BitVec 32).toNat = 64 := rfl
        bve_lets
        refine wp_call_of_spec _ _ (hExtNeed _ _ _ X ?_)
        simp only [vals_nil, vals_cons, Arg.val_var, Arg.val_imm]
        refine ⟨c, s2, R, rfl, hinv2.1, (by rw [h0_32]; omega),
          entries_to_extNeed hinv2 (off := 0) (lit := 2 * v.toNat) (fun i hi => by
            rw [Nat.zero_add]; exact hp_ok i hi),
          hm2, ?_⟩
        intro en1
        bve_lets
        refine wp_call_of_spec _ _ (hExtNeed _ _ _ X ?_)
        simp only [vals_nil, vals_cons, Arg.val_var, Arg.val_imm]
        refine ⟨c, s2, R, rfl, hinv2.1, (by rw [h64_32]; omega),
          entries_to_extNeed hinv2 (off := 64) (lit := 2 * v.toNat + 1) hn_ok,
          hm2, ?_⟩
        intro en2
        bve_ld load_full_extend_len hm2
        bve_ld load_full_extend_cap hm2
        bve_lets
        refine wp_join_group (ts := []) (fun _ ml => ml = m2) ?_ ?_
        · rintro J _ ml h_ml; subst ml
          rw [Blocks.get_here]
          bve_lets
          bve_ld load_full_elim_bound hm2
          bve_lets
          -- Join after `if (fit)`
          refine wp_join_group (ts := [i64, i64, .bool]) (fun (_rc_f, rp_f, fit_f, _) ml =>
              ∃ sf,
                FullDenseInvW c F0 F_cur sf ∧ sf.core.cur_vars = s2.core.cur_vars ∧
                sf.core.fuel = s2.core.fuel ∧
                sf.core.arena = s2.core.arena ∧ sf.core.arena_len = s2.core.arena_len ∧
                (∀ idx < 96, sf.scratch.scratch_buf[idx]? = scr2[idx]?) ∧
                (fit_f = true →
                  160 ≤ rp_f.toNat ∧ rp_f.toNat ≤ c.scratch_cap ∧
                  FullResBufOkW F_cur sf rp_f.toNat 160) ∧
                (FullMem c sf ⋆ R) ml) ?_ ?_
          · rintro J_fit ⟨rc_f, rp_f, fit_f, ⟨⟩⟩ ml ⟨sf, hinvf, hcvf, hflf, harf, half, hbuf_f,
                hres_f, hmf⟩
            rw [Blocks.get_here]
            bve_lets
            -- Join entering BCE fallback (`J_bce_entry`, `ts := []`)
            refine wp_join_group (ts := []) (fun _ m_bce =>
                ∃ sb,
                  FullDenseInvW c F0 F_cur sb ∧ sb.core.cur_vars = s2.core.cur_vars ∧
                  sb.core.fuel = s2.core.fuel ∧
                  sb.core.arena = s2.core.arena ∧ sb.core.arena_len = s2.core.arena_len ∧
                  (∀ idx < 96, sb.scratch.scratch_buf[idx]? = scr2[idx]?) ∧
                  (FullMem c sb ⋆ R) m_bce) ?_ ?_
            · rintro J_bce _ m_bce ⟨sb, hinvb, hcvb, hflb, harb, halb, hbuf_b, hmb⟩
              rw [Blocks.get_here]
              bve_lets
              have hpbce : ∀ i < np.toNat, FullBveTryBceEntryOk c sb (scr2[i]?.getD 0#32) :=
                fun i hi => FullBveTryBceEntryOk.with_same_arena harb halb
                  (FullBveEntryOkW.to_tryBceEntry hinv2 (hp_ok i hi))
              have hnbce : ∀ j < nn.toNat, FullBveTryBceOppOk c sb (scr2[64 + j]?.getD 0#32) :=
                fun j hj => FullBveTryBceOppOk.with_same_arena harb halb
                  (FullBveEntryOkW.to_tryBceOpp hinv2 (hn_ok j hj))
              refine wp_loop_inv (ts := [i32])
                (fun (i, _) ml =>
                  ∃ sl,
                    FullDenseInvW c F0 F_cur sl ∧ sl.core.cur_vars = s.core.cur_vars ∧
                    sl.core.fuel = s.core.fuel ∧ i.toNat ≤ np.toNat ∧
                    (∀ idx < 96, sl.scratch.scratch_buf[idx]? = scr2[idx]?) ∧
                    (∀ k < np.toNat, FullBveTryBceEntryOk c sl (scr2[k]?.getD 0#32)) ∧
                    (∀ j < nn.toNat, FullBveTryBceOppOk c sl (scr2[64 + j]?.getD 0#32)) ∧
                    (FullMem c sl ⋆ R) ml)
                (fun (i, _) _ => np.toNat - i.toNat)
                (fun Jlp hJlp => by
                  bve_jump
                  exact hJlp (0#32, PUnit.unit) m_bce
                    ⟨sb, hinvb, by rw [hcvb, hs2_cv], by rw [hflb, hs2_fl],
                      Nat.zero_le _, hbuf_b, hpbce, hnbce, hmb⟩)
                (fun Jlp ⟨i, ⟨⟩⟩ ml ⟨sl, hinvl, hcvl, hfll, hi_le, hbuf_l, hpk, hnj, hml⟩ ihlp => by
                  rw [Blocks.get_here]
                  bve_jnz hi_lt
                  · have hi_nat : i.toNat < np.toNat := by
                      rw [BitVec.ult, decide_eq_true_eq] at hi_lt; exact hi_lt
                    have hscrl := hinvl.1.scratch_ok.scratch_buf_len
                    have harl := hinvl.1.core_ok.arena_len_arr
                    have harle := hinvl.1.core_ok.arena_len_le
                    have hi_scr : (i.setWidth 64).toNat < sl.scratch.scratch_buf.length := by
                      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : i.toNat < 2 ^ 64)]
                      omega
                    have hi_eq : (i.setWidth 64).toNat = i.toNat := by
                      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : i.toNat < 2 ^ 64)]
                    have hwi_eq : sl.scratch.scratch_buf[i.toNat]'(by omega) =
                        scr2[i.toNat]?.getD 0#32 := by
                      have := hbuf_l i.toNat (by omega)
                      rw [List.getElem?_eq_getElem
                        (by omega : i.toNat < sl.scratch.scratch_buf.length)] at this
                      rw [← this]; rfl
                    refine wp_join_group (ts := []) (fun _ mn =>
                        ∃ sn,
                          FullDenseInvW c F0 F_cur sn ∧ sn.core.cur_vars = s.core.cur_vars ∧
                          sn.core.fuel = s.core.fuel ∧
                          (∀ idx < 96, sn.scratch.scratch_buf[idx]? = scr2[idx]?) ∧
                          (∀ k < np.toNat, FullBveTryBceEntryOk c sn (scr2[k]?.getD 0#32)) ∧
                          (∀ j < nn.toNat, FullBveTryBceOppOk c sn (scr2[64 + j]?.getD 0#32)) ∧
                          (FullMem c sn ⋆ R) mn) ?_ ?_
                    · rintro Jnxt _ mn ⟨sn, hinvn, hcvn, hfln, hbuf_n, hpkn, hnjn, hmn⟩
                      rw [Blocks.get_here]
                      bve_jump
                      have hi1 : (i + 1#32).toNat = i.toNat + 1 := by
                        rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
                          Nat.mod_eq_of_lt (by omega : i.toNat + 1 < 2 ^ 32)]
                      exact ihlp (i + 1#32, PUnit.unit) mn (by dsimp only; rw [hi1]; omega)
                        ⟨sn, hinvn, hcvn, hfln, by rw [hi1]; omega, hbuf_n, hpkn, hnjn, hmn⟩
                    · intro Jnxt hJnxt
                      bve_ld (c0_load_full_scratch_buf (i := i.setWidth 64) hi_scr hml)
                      bve_lets
                      refine wp_call_of_spec _ _ (hTryBce _ _ _ X ?_)
                      simp only [vals_nil, vals_cons, Arg.val_var, Arg.val_imm]
                      refine ⟨c, F0, F_cur, sl, R, rfl, hinvl,
                        (by change pl.toNat < 2 * sl.core.cur_vars; rw [hpl_nat, hcvl]; omega),
                        (by simp only [hi_eq]; rw [hwi_eq]; exact hpk i.toNat hi_nat),
                        (by rw [h64_32]; omega),
                        (fun j hj => by
                          rw [h64_32, hbuf_l (64 + j) (by omega)]; exact hnj j hj),
                        hml, ?_⟩
                      rintro blk lm' tmp' m_tb stb hinv_tb hm_tb
                      have htb_p : ∀ k < np.toNat,
                          FullBveTryBceEntryOk c stb (scr2[k]?.getD 0#32) :=
                        (full_bve_tryBce_pres (s := sl) (s' := stb) rfl rfl hpk hnj).1
                      have htb_n : ∀ j < nn.toNat,
                          FullBveTryBceOppOk c stb (scr2[64 + j]?.getD 0#32) :=
                        (full_bve_tryBce_pres (s := sl) (s' := stb) rfl rfl hpk hnj).2
                      have htb_scr_len : stb.scratch.scratch_buf.length = c.scratch_cap := hscrl
                      have htb_scr_idx : (i.setWidth 64).toNat < stb.scratch.scratch_buf.length :=
                        hi_scr
                      bve_jnz hblk
                      · refine wp_join_group (ts := []) (fun _ mn =>
                            ∃ sn,
                              FullDenseInvW c F0 F_cur sn ∧
                              sn.core.cur_vars = s.core.cur_vars ∧
                              sn.core.fuel = s.core.fuel ∧
                              (∀ idx < 96, sn.scratch.scratch_buf[idx]? = scr2[idx]?) ∧
                              (∀ k < np.toNat, FullBveTryBceEntryOk c sn (scr2[k]?.getD 0#32)) ∧
                              (∀ j < nn.toNat, FullBveTryBceOppOk c sn (scr2[64 + j]?.getD 0#32)) ∧
                              (FullMem c sn ⋆ R) mn) ?_ ?_
                        · rintro J_try _ mn hmn
                          rw [Blocks.get_here]; bve_jump; exact hJnxt () mn hmn
                        · intro J_try hJ_try
                          bve_ld (c0_load_full_scratch_buf (i := i.setWidth 64)
                            htb_scr_idx hm_tb)
                          bve_jnz hbin_flag
                          · -- Binary BCE branch
                            refine wp_join_group (ts := []) (fun _ mn =>
                                ∃ sn,
                                  FullDenseInvW c F0 F_cur sn ∧
                                  sn.core.cur_vars = s.core.cur_vars ∧
                                  sn.core.fuel = s.core.fuel ∧
                                  (∀ idx < 96, sn.scratch.scratch_buf[idx]? = scr2[idx]?) ∧
                                  (∀ k < np.toNat,
                                    FullBveTryBceEntryOk c sn (scr2[k]?.getD 0#32)) ∧
                                  (∀ j < nn.toNat,
                                    FullBveTryBceOppOk c sn (scr2[64 + j]?.getD 0#32)) ∧
                                  (FullMem c sn ⋆ R) mn) ?_ ?_
                            · rintro Jb _ mn hmn
                              rw [Blocks.get_here]; bve_jump; exact hJ_try () mn hmn
                            · intro Jb hJb
                              bve_ld (c0_load_full_scratch_buf (i := i.setWidth 64)
                                htb_scr_idx hm_tb)
                              bve_lets
                              refine wp_call_of_spec _ _ (hExtPush2 _ _ _ X ?_)
                              simp only [vals_nil, vals_cons, Arg.val_var]
                              refine ⟨c, stb, R, ⟨rfl, hinv_tb.2.2.2.2.1.2⟩, hinv_tb.1, hm_tb, ?_⟩
                              rintro ⟨okp, ⟨⟩⟩ se2 m_e2 hcore_e2 hlen_e2
                                ⟨hll_e2, hext_e2, hscr_e2⟩ hm_e2
                              change (FullMem c se2 ⋆ R) m_e2 at hm_e2
                              have heq_e2 : se2.core = stb.core :=
                                fullCoreState_agrees_with_scratch hcore_e2
                              have hinv_e2 : FullDenseInvW c F0 F_cur se2 :=
                                denseInvW_of_extPush hinv_tb hlen_e2 hcore_e2 hll_e2 hext_e2
                              have he2_p : ∀ k < np.toNat,
                                  FullBveTryBceEntryOk c se2 (scr2[k]?.getD 0#32) :=
                                (full_bve_tryBce_pres (s := stb) (s' := se2)
                                  (congrArg FullCoreState.arena heq_e2)
                                  (congrArg FullCoreState.arena_len heq_e2) htb_p htb_n).1
                              have he2_n : ∀ j < nn.toNat,
                                  FullBveTryBceOppOk c se2 (scr2[64 + j]?.getD 0#32) :=
                                (full_bve_tryBce_pres (s := stb) (s' := se2)
                                  (congrArg FullCoreState.arena heq_e2)
                                  (congrArg FullCoreState.arena_len heq_e2) htb_p htb_n).2
                              have hcv_e2 : se2.core.cur_vars = s.core.cur_vars := by
                                rw [heq_e2]; exact hcvl
                              have hfl_e2 : se2.core.fuel = s.core.fuel := by
                                rw [heq_e2]; exact hfll
                              have hbuf_e2 : ∀ idx < 96,
                                  se2.scratch.scratch_buf[idx]? = scr2[idx]? :=
                                fun idx hi => by rw [hscr_e2]; exact hbuf_l idx hi
                              bve_jnz hokp
                              · bve_ld (c0_load_full_scratch_buf (i := i.setWidth 64)
                                    (by rw [hinv_e2.1.scratch_ok.scratch_buf_len]; omega) hm_e2)
                                bve_lets
                                refine wp_call_of_spec _ _ (hDelBin _ _ _ X ?_)
                                simp only [vals_nil, vals_cons, Arg.val_var]
                                refine ⟨c, se2, R, rfl, hinv_e2.1, hinv_e2.2.1.watches.layout,
                                  hm_e2, ?_⟩
                                rintro wvec' wstk' wu' nb' m_db sdb hlen_db hlay_db hwat_fn hm_db
                                have hinv_db : FullDenseInvW c F0 F_cur sdb :=
                                  FullDenseInvW.of_deleteBinary hinv_e2 hlen_db
                                    (hwat_fn F_cur hinv_e2.2.1.watches)
                                have hdb_p : ∀ k < np.toNat,
                                    FullBveTryBceEntryOk c sdb (scr2[k]?.getD 0#32) :=
                                  (full_bve_tryBce_pres (s := se2) (s' := sdb) rfl rfl
                                    he2_p he2_n).1
                                have hdb_n : ∀ j < nn.toNat,
                                    FullBveTryBceOppOk c sdb (scr2[64 + j]?.getD 0#32) :=
                                  (full_bve_tryBce_pres (s := se2) (s' := sdb) rfl rfl
                                    he2_p he2_n).2
                                bve_ld load_full_bce_cnt hm_db
                                bve_st m_bce1, hm_bce1 := store_full_bce_cnt
                                  (sdb.scratch.bce_cnt + 1#64) hm_db
                                bve_jump
                                let sbce : FullState :=
                                  { sdb with scratch :=
                                    { sdb.scratch with bce_cnt := sdb.scratch.bce_cnt + 1#64 } }
                                have hbce_p : ∀ k < np.toNat,
                                    FullBveTryBceEntryOk c sbce (scr2[k]?.getD 0#32) :=
                                  (full_bve_tryBce_pres (s := sdb) (s' := sbce) rfl rfl
                                    hdb_p hdb_n).1
                                have hbce_n : ∀ j < nn.toNat,
                                    FullBveTryBceOppOk c sbce (scr2[64 + j]?.getD 0#32) :=
                                  (full_bve_tryBce_pres (s := sdb) (s' := sbce) rfl rfl
                                    hdb_p hdb_n).2
                                exact hJb () m_bce1 ⟨sbce, FullDenseInvW.with_bce_cnt hinv_db _,
                                  hcv_e2, hfl_e2, hbuf_e2, hbce_p, hbce_n, hm_bce1⟩
                              · bve_jump
                                exact hJb () m_e2 ⟨se2, hinv_e2, hcv_e2, hfl_e2, hbuf_e2, he2_p,
                                  he2_n, hm_e2⟩
                          · -- Large clause BCE branch (`PH_GARB`)
                            refine wp_join_group (ts := []) (fun _ mn =>
                                ∃ sn,
                                  FullDenseInvW c F0 F_cur sn ∧
                                  sn.core.cur_vars = s.core.cur_vars ∧
                                  sn.core.fuel = s.core.fuel ∧
                                  (∀ idx < 96, sn.scratch.scratch_buf[idx]? = scr2[idx]?) ∧
                                  (∀ k < np.toNat,
                                    FullBveTryBceEntryOk c sn (scr2[k]?.getD 0#32)) ∧
                                  (∀ j < nn.toNat,
                                    FullBveTryBceOppOk c sn (scr2[64 + j]?.getD 0#32)) ∧
                                  (FullMem c sn ⋆ R) mn) ?_ ?_
                            · rintro Jl _ mn hmn
                              rw [Blocks.get_here]; bve_jump; exact hJ_try () mn hmn
                            · intro Jl hJl
                              bve_ld (c0_load_full_scratch_buf (i := i.setWidth 64)
                                htb_scr_idx hm_tb)
                              bve_lets
                              refine wp_call_of_spec _ _ (hExtPushCl _ _ _ X ?_)
                              simp only [vals_nil, vals_cons, Arg.val_var]
                              refine ⟨c, stb, R, ⟨rfl, hinv_tb.2.2.2.2.1.2⟩, hinv_tb.1, hm_tb, ?_⟩
                              rintro ⟨okp, ⟨⟩⟩ se2 m_e2 hcore_e2 hlen_e2
                                ⟨hll_e2, hext_e2, hscr_e2⟩ hm_e2
                              change (FullMem c se2 ⋆ R) m_e2 at hm_e2
                              have heq_e2 : se2.core = stb.core :=
                                fullCoreState_agrees_with_scratch hcore_e2
                              have hinv_e2 : FullDenseInvW c F0 F_cur se2 :=
                                denseInvW_of_extPush hinv_tb hlen_e2 hcore_e2 hll_e2 hext_e2
                              have he2_p : ∀ k < np.toNat,
                                  FullBveTryBceEntryOk c se2 (scr2[k]?.getD 0#32) :=
                                (full_bve_tryBce_pres (s := stb) (s' := se2)
                                  (congrArg FullCoreState.arena heq_e2)
                                  (congrArg FullCoreState.arena_len heq_e2) htb_p htb_n).1
                              have he2_n : ∀ j < nn.toNat,
                                  FullBveTryBceOppOk c se2 (scr2[64 + j]?.getD 0#32) :=
                                (full_bve_tryBce_pres (s := stb) (s' := se2)
                                  (congrArg FullCoreState.arena heq_e2)
                                  (congrArg FullCoreState.arena_len heq_e2) htb_p htb_n).2
                              have hcv_e2 : se2.core.cur_vars = s.core.cur_vars :=
                                heq_e2 ▸ hcvl
                              have hfl_e2 : se2.core.fuel = s.core.fuel := heq_e2 ▸ hfll
                              have hbuf_e2 : ∀ idx < 96,
                                  se2.scratch.scratch_buf[idx]? = scr2[idx]? :=
                                fun idx hi => by rw [hscr_e2]; exact hbuf_l idx hi
                              bve_jnz hokp
                              · have hscr_e2_len := hinv_e2.1.scratch_ok.scratch_buf_len
                                have har_e2_len := hinv_e2.1.core_ok.arena_len_arr
                                have har_e2_le := hinv_e2.1.core_ok.arena_len_le
                                bve_ld load_full_arena_ptr hm_e2
                                bve_ld (c0_load_full_scratch_buf (i := i.setWidth 64)
                                    (by rw [hscr_e2_len]; omega) hm_e2)
                                let ccr := se2.scratch.scratch_buf[(i.setWidth 64).toNat]'(by
                                  rw [hscr_e2_len]; omega)
                                have hccr_eq : ccr = scr2[i.toNat]?.getD 0#32 := by
                                  have hli :
                                      (i.setWidth 64).toNat < se2.scratch.scratch_buf.length := by
                                    rw [hscr_e2_len]; omega
                                  have h0 : se2.scratch.scratch_buf[i.toNat]? = some ccr := by
                                    rw [← hi_eq, List.getElem?_eq_getElem hli]
                                  have h1 := h0.symm.trans (hbuf_e2 i.toNat (by omega))
                                  rw [← h1]; rfl
                                have hnb_ccr : (ccr &&& 0x80000000#32) = 0#32 := by
                                  have h0 : (stb.scratch.scratch_buf[(i.setWidth 64).toNat]'
                                      htb_scr_idx &&& 0x80000000#32) = 0#32 := by
                                    exact bne_eq_false_iff_eq.mp hbin_flag
                                  simpa only [ccr, hscr_e2] using h0
                                have hbce_ccr := he2_p i.toNat hi_nat
                                rw [← hccr_eq] at hbce_ccr
                                unfold FullBveTryBceEntryOk at hbce_ccr
                                simp only [hnb_ccr, ne_eq, not_true_eq_false, ↓reduceIte]
                                  at hbce_ccr
                                have hccr_ar :
                                    (ccr.setWidth 64).toNat < se2.core.arena.length := by
                                  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt
                                    (by have := ccr.isLt; omega : ccr.toNat < 2 ^ 64)]
                                  omega
                                have hccr_nat : (ccr.setWidth 64).toNat = ccr.toNat := by
                                  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt
                                    (by have := ccr.isLt; omega : ccr.toNat < 2 ^ 64)]
                                have hccr_sz : 3 ≤ fullArenaClauseSize se2 ccr.toNat :=
                                  (hinv_e2.2.1.arena.refs_wf ccr.toNat hbce_ccr.1).2.1
                                have hccr_p2 : ((ccr.setWidth 64) + 2#64).toNat <
                                    se2.core.arena.length := by
                                  rw [BitVec.toNat_add, show (2#64 : BitVec 64).toNat = 2 from rfl,
                                    hccr_nat, Nat.mod_eq_of_lt (by omega : ccr.toNat + 2 < 2 ^ 64)]
                                  unfold fullArenaClauseSize fullArenaClauseSizeCore at hbce_ccr
                                  omega
                                have hhdr_eq : se2.core.arena[(ccr.setWidth 64).toNat]'hccr_ar =
                                    fullArenaHdr se2 ccr.toNat := by
                                  unfold fullArenaHdr fullArenaHdrCore
                                  rw [← hccr_nat, List.getElem?_eq_getElem hccr_ar,
                                    Option.getD_some]
                                have har_eq :
                                    se2.core.arena.set (ccr.setWidth 64).toNat
                                      (se2.core.arena[(ccr.setWidth 64).toNat]'hccr_ar |||
                                        0x00080000#32) =
                                    se2.core.arena.set ccr.toNat
                                      (fullArenaHdr se2 ccr.toNat ||| 0x00080000#32) := by
                                  rw [hhdr_eq, hccr_nat]
                                bve_ld (c0_load_full_arena (i := ccr.setWidth 64) hccr_ar hm_e2)
                                bve_st m_ar, hm_ar := c0_store_full_arena (i := ccr.setWidth 64)
                                  (se2.core.arena[(ccr.setWidth 64).toNat]'hccr_ar |||
                                    0x00080000#32) hccr_ar hm_e2
                                bve_ld load_full_arena_garbage hm_ar
                                bve_ld (c0_load_full_arena (i := ccr.setWidth 64 + 2#64)
                                  (by rw [List.length_set]; exact hccr_p2) hm_ar)
                                bve_st m_ag, hm_ag := store_full_arena_garbage _ hm_ar
                                bve_ld load_full_bce_cnt hm_ag
                                bve_st m_bce1, hm_bce1 := store_full_bce_cnt _ hm_ag
                                bve_jump
                                simp only [har_eq] at hm_bce1
                                let ar_mg := se2.core.arena.set ccr.toNat
                                  (fullArenaHdr se2 ccr.toNat ||| 0x00080000#32)
                                let ag_mg := se2.core.arena_garbage + 3#64 +
                                  (ar_mg[((ccr.setWidth 64) + 2#64).toNat]'(by
                                    rw [List.length_set]; exact hccr_p2)).setWidth 64
                                let smg : FullState :=
                                  { se2 with
                                    core := { se2.core with arena := ar_mg, arena_garbage := ag_mg }
                                    scratch := { se2.scratch with
                                      bce_cnt := se2.scratch.bce_cnt + 1#64 } }
                                have hinv_mg := FullDenseInvW.with_bce_cnt
                                  (FullDenseInvW.of_markGarb_zero hinv_e2 hbce_ccr.1 ag_mg)
                                  (se2.scratch.bce_cnt + 1#64)
                                have htbe := full_bve_tryBce_of_markGarb hinv_e2.1
                                  hinv_e2.2.1 hbce_ccr.1 ag_mg he2_p he2_n
                                have hmg_p : ∀ k < np.toNat,
                                    FullBveTryBceEntryOk c smg (scr2[k]?.getD 0#32) :=
                                  (full_bve_tryBce_pres (s' := smg) rfl rfl htbe.1 htbe.2).1
                                have hmg_n : ∀ j < nn.toNat,
                                    FullBveTryBceOppOk c smg (scr2[64 + j]?.getD 0#32) :=
                                  (full_bve_tryBce_pres (s' := smg) rfl rfl htbe.1 htbe.2).2
                                exact hJl () m_bce1 ⟨smg, hinv_mg, hcv_e2, hfl_e2, hbuf_e2,
                                  hmg_p, hmg_n, hm_bce1⟩
                              · bve_jump
                                exact hJl () m_e2 ⟨se2, hinv_e2, hcv_e2, hfl_e2, hbuf_e2, he2_p,
                                  he2_n, hm_e2⟩
                      · bve_jump
                        exact hJnxt () m_tb ⟨stb, hinv_tb, hcvl, hfll, hbuf_l, htb_p, htb_n, hm_tb⟩
                  · -- Loop exit ¬ i < np -> return 1
                    bve_ret
                    exact hQ 1#64 sl ml hinvl.toDense (by rw [← hcvl]; exact Nat.le_refl _)
                      (by rw [← hfll]; exact Nat.le_refl _) (Or.inl rfl)
                      (fun h => by cases h) hml)
            · intro J_bce hJ_bce
              bve_jnz hfit_c
              · bve_ld load_full_arena_len hmf
                bve_ld load_full_arena_cap hmf
                bve_jnz har_fit
                · refine wp_join_group (ts := []) (fun _ m_o =>
                      ∃ so, FullDenseInvW c F0 F_cur so ∧ so.core.cur_vars = s.core.cur_vars ∧
                        so.core.fuel = s.core.fuel ∧ (FullMem c so ⋆ R) m_o) ?_ ?_
                  · rintro J_oom2 _ m_o ⟨so, hinvo, hcvo, hflo, hmo⟩
                    rw [Blocks.get_here]
                    bve_st m_o1, hm_o1 := store_full_oom 1#64 hmo
                    bve_ret
                    exact hQ 2#64 _ m_o1 (FullDenseInvW.with_oom hinvo 1#64).toDense
                      (by rw [← hcvo]; exact Nat.le_refl _) (by rw [← hflo]; exact Nat.le_refl _)
                      (Or.inr (Or.inl rfl)) (fun h => by cases h) hm_o1
                  · intro J_oom2 hJ_oom2
                    refine wp_call_of_spec _ _ (hWeaken _ _ _ X ?_)
                    simp only [vals_nil, vals_cons, Arg.val_var, Arg.val_imm]
                    refine ⟨c, F0, F_cur, sf, R, rfl, hinvf,
                      (by change pl.toNat < 2 * sf.core.cur_vars
                          rw [hpl_nat, hcvf, hs2_cv]; omega),
                      (by rw [h0_32]; omega),
                      (fun i hi => by
                        rw [h0_32, Nat.zero_add, hbuf_f i (by omega)]
                        exact fullBveWeakItemOk_of_pres (by rw [hcvf, hs2_cv])
                          (by unfold fullArenaClauseRefs fullArenaClauseRefsCore
                              rw [harf, half])
                          (FullBveEntryOkW.to_weak (hp_ok i hi))),
                      hmf, ?_⟩
                    intro ok1 sf1 m_w1 hinvf1 hcv1 hfl1 hscr1 hrefs1 hm_w1
                    bve_jnz hok1
                    · refine wp_call_of_spec _ _ (hWeaken _ _ _ X ?_)
                      simp only [vals_nil, vals_cons, Arg.val_var, Arg.val_imm]
                      refine ⟨c, F0, F_cur, sf1, R, rfl, hinvf1,
                        (by change (pl ||| 1#32).toNat < 2 * sf1.core.cur_vars
                            rw [hnl_nat, hcv1, hcvf, hs2_cv]; omega),
                        (by rw [h64_32]; omega),
                        (fun j hj => by
                          rw [h64_32, hscr1, hbuf_f (64 + j) (by omega)]
                          exact fullBveWeakItemOk_of_pres (by rw [hcv1, hcvf, hs2_cv])
                            (hrefs1.trans (by
                              unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [harf, half]))
                            (FullBveEntryOkW.to_weak (hn_ok j hj))),
                        hm_w1, ?_⟩
                      intro ok2 sf2 m_w2 hinvf2 hcv2 hfl2 hscr2 _hrefs2 hm_w2
                      bve_jnz hok2
                      · refine wp_call_of_spec _ _ (hSetInact _ _ _ X ?_)
                        simp only [vals_nil, vals_cons, Arg.val_var, Arg.val_imm]
                        refine ⟨c, sf2, R, rfl, hinvf2.1, hm_w2, ?_⟩
                        intro flags' unass' m_si hfl_len hm_si
                        let sf3 : FullState :=
                          { sf2 with core := { sf2.core with flags := flags',
                                                             unassigned := unass' } }
                        have hinvf3 := FullDenseInvW.with_flags_unassigned hinvf2 hfl_len unass'
                        bve_ld load_full_bve_cnt hm_si
                        bve_st m_bve, hm_bve := store_full_bve_cnt
                          (sf3.scratch.bve_cnt + 1#64) hm_si
                        bve_lets
                        let sf4 : FullState :=
                          { sf3 with scratch := { sf3.scratch with
                              bve_cnt := sf3.scratch.bve_cnt + 1#64 } }
                        have hinvf4 := FullDenseInvW.with_bve_cnt hinvf3
                          (sf3.scratch.bve_cnt + 1#64)
                        obtain ⟨hrp160, hrp_cap, hres_fit⟩ := hres_f hfit_c
                        have hres4 : FullResBufOkW F_cur sf4 rp_f.toNat 160 :=
                          FullResBufOkW.with_state
                            (by dsimp only [sf4, sf3]; exact hcv2.trans hcv1)
                            (fun idx hidx => by
                              dsimp only [sf4, sf3]
                              rw [hscr2, hscr1])
                            hres_fit
                        refine wp_call_of_spec _ _ (hCommitRes _ _ _ X ?_)
                        simp only [vals_nil, vals_cons, Arg.val_var, Arg.val_imm]
                        refine ⟨c, F0, F_cur, sf4, R, rfl, hinvf4,
                          (by rw [show (160 : BitVec 64).toNat = 160 from rfl]; exact hrp160),
                          hrp_cap,
                          (by rw [show (160 : BitVec 64).toNat = 160 from rfl]; exact hres4),
                          hm_bve, ?_⟩
                        intro r_cr sf_end m_end hinv_cr hcv_cr hfl_cr hrc_cr h20_cr hm_end
                        exact hQ r_cr sf_end m_end hinv_cr.toDense
                          (by rw [hcv_cr]; dsimp only [sf4, sf3]
                              rw [hcv2, hcv1, hcvf, hs2_cv]; exact Nat.le_refl _)
                          (by rw [hfl_cr]; dsimp only [sf4, sf3]
                              rw [hfl2, hfl1, hflf, hs2_fl]; exact Nat.le_refl _)
                          hrc_cr h20_cr hm_end
                      · bve_jump; exact hJ_oom2 () m_w2 ⟨sf2, hinvf2,
                          by rw [hcv2, hcv1, hcvf, hs2_cv],
                          by rw [hfl2, hfl1, hflf, hs2_fl], hm_w2⟩
                    · bve_jump; exact hJ_oom2 () m_w1 ⟨sf1, hinvf1,
                        by rw [hcv1, hcvf, hs2_cv], by rw [hfl1, hflf, hs2_fl], hm_w1⟩
                · bve_jump; exact hJ_bce () ml ⟨sf, hinvf, hcvf, hflf, harf, half,
                    (fun idx hidx => hbuf_f idx (by omega)), hmf⟩
              · bve_jump; exact hJ_bce () ml ⟨sf, hinvf, hcvf, hflf, harf, half,
                  (fun idx hidx => hbuf_f idx (by omega)), hmf⟩
          · intro J_fit hJ_fit
            bve_jnz hfit0
            · have hsc132 : 132 ≤ c.scratch_cap := by omega
              refine wp_call_of_spec _ _ (hGates _ _ _ X ?_)
              simp only [vals_nil, vals_cons, Arg.val_var]
              refine ⟨c, F0, F_cur, s2, R, rfl, hinv2, hsc132, hv_lt, (by omega), (by omega),
                hp_ok, hn_ok, hm2, ?_⟩
              dsimp only
              rintro lm3 scr3 m3 hinv3 hkeep3 hm3
              let s3 : FullState :=
                { s2 with
                  core := { s2.core with lit_mark := lm3 }
                  scratch := { s2.scratch with scratch_buf := scr3 } }
              have hsc3_len := hinv3.1.scratch_ok.scratch_buf_len
              bve_ld (load_full_scratch_buf (i := 128) (by omega) hm3)
              bve_ld (load_full_scratch_buf (i := 129) (by omega) hm3)
              bve_ld (load_full_scratch_buf (i := 130) (by omega) hm3)
              bve_ld (load_full_scratch_buf (i := 131) (by omega) hm3)
              bve_lets
              have hsc3_idx : ∀ idx < c.scratch_cap, (idx < 128 ∨ 132 ≤ idx) →
                  scr3[idx]? = scr2[idx]? := fun idx hidx hb => hkeep3 idx hidx hb
              have hs3_buf : ∀ idx < 96, s3.scratch.scratch_buf[idx]? = scr2[idx]? :=
                fun idx hidx => hsc3_idx idx (by omega) (Or.inl (by omega))
              refine wp_loop_inv (ts := [i64, i64, .bool, i32])
                (fun (rc, rp, fit_i, i, _) ml =>
                  ∃ sf,
                    FullDenseInvW c F0 F_cur sf ∧ sf.core.cur_vars = s2.core.cur_vars ∧
                    sf.core.fuel = s2.core.fuel ∧
                    sf.core.arena = s2.core.arena ∧ sf.core.arena_len = s2.core.arena_len ∧
                    (∀ idx < 96, sf.scratch.scratch_buf[idx]? = scr2[idx]?) ∧
                    i.toNat ≤ np.toNat ∧
                    (fit_i = true →
                      160 ≤ rp.toNat ∧ rp.toNat ≤ c.scratch_cap ∧
                      FullResBufOkW F_cur sf rp.toNat 160) ∧
                    (FullMem c sf ⋆ R) ml)
                (fun (_, _, fit_i, i, _) _ =>
                  if fit_i then np.toNat - i.toNat + 1 else 0)
                (fun Jlp hJlp => by
                  bve_jump
                  exact hJlp (0#64, 160#64,
                      (BitVec.ofNat 64 s1.scratch.extend_len + (en1 + en2)).ule
                        (BitVec.ofNat 64 c.extend_cap), 0#32, ()) m3
                    ⟨s3, hinv3, rfl, rfl, rfl, rfl, hs3_buf, Nat.zero_le _,
                      fun _ => ⟨by rw [show (160#64 : BitVec 64).toNat = 160 from rfl]; omega,
                        by rw [show (160#64 : BitVec 64).toNat = 160 from rfl]; omega,
                        by rw [show (160#64 : BitVec 64).toNat = 160 from rfl]; exact .nil⟩,
                      hm3⟩)
                (fun Jlp ⟨rc, rp, fit_i, i, ⟨⟩⟩ ml
                    ⟨sf, hinvf, hcvf, hflf, harf, half, hbuf_f, hi_le, hres_f, hml⟩ ihlp => by
                  rw [Blocks.get_here]
                  bve_jnz hi_lt
                  · bve_jnz hfit_i
                    · have hi_nat : i.toNat < np.toNat := by
                        rw [BitVec.ult, decide_eq_true_eq] at hi_lt; exact hi_lt
                      have hhi1 : (i + 1#32).toNat = i.toNat + 1 := by
                        rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
                          Nat.mod_eq_of_lt (by omega : i.toNat + 1 < 2 ^ 32)]
                      refine wp_join_group (ts := [i64, i64, .bool, i32])
                          (fun (rc_n, rp_n, fit_n, _, _) mn =>
                          ∃ sn,
                            FullDenseInvW c F0 F_cur sn ∧ sn.core.cur_vars = s2.core.cur_vars ∧
                            sn.core.fuel = s2.core.fuel ∧
                            sn.core.arena = s2.core.arena ∧ sn.core.arena_len = s2.core.arena_len ∧
                            (∀ idx < 96, sn.scratch.scratch_buf[idx]? = scr2[idx]?) ∧
                            (fit_n = true →
                              160 ≤ rp_n.toNat ∧ rp_n.toNat ≤ c.scratch_cap ∧
                              FullResBufOkW F_cur sn rp_n.toNat 160) ∧
                            (FullMem c sn ⋆ R) mn) ?_ ?_
                      · rintro Js ⟨rc_n, rp_n, fit_n, _j_n, ⟨⟩⟩ mn
                          ⟨sn, hinvn, hcvn, hfln, harn, haln, hbuf_n, hres_n, hmn⟩
                        rw [Blocks.get_here]
                        bve_jump
                        exact ihlp (rc_n, rp_n, fit_n, i + 1#32, ()) mn (by
                          dsimp only; cases fit_n <;> cases hfit_i <;> simp [hhi1]; omega)
                          ⟨sn, hinvn, hcvn, hfln, harn, haln, hbuf_n, by rw [hhi1]; omega,
                            hres_n, hmn⟩
                      · intro Js hJs
                        obtain ⟨hrp_160, hrp_cap, hres_fit⟩ := hres_f hfit_i
                        refine wp_loop_inv (ts := [i64, i64, i32])
                          (fun (rc_j, rp_j, j, _) mj =>
                            ∃ sj,
                              FullDenseInvW c F0 F_cur sj ∧ sj.core.cur_vars = s2.core.cur_vars ∧
                              sj.core.fuel = s2.core.fuel ∧
                              sj.core.arena = s2.core.arena ∧
                              sj.core.arena_len = s2.core.arena_len ∧
                              (∀ idx < 96, sj.scratch.scratch_buf[idx]? = scr2[idx]?) ∧
                              j.toNat ≤ nn.toNat ∧
                              160 ≤ rp_j.toNat ∧ rp_j.toNat ≤ c.scratch_cap ∧
                              FullResBufOkW F_cur sj rp_j.toNat 160 ∧
                              (FullMem c sj ⋆ R) mj)
                          (fun (_, _, j, _) _ => nn.toNat - j.toNat)
                          (fun Js1 hJs1 => by
                            bve_jump
                            exact hJs1 (rc, rp, 0#32, ()) ml
                              ⟨sf, hinvf, hcvf, hflf, harf, half, hbuf_f, Nat.zero_le _,
                                hrp_160, hrp_cap, hres_fit, hml⟩)
                          (fun Js1 ⟨rc_j, rp_j, j, ⟨⟩⟩ mj
                              ⟨sj, hinvj, hcvj, hflj, harj, halj, hbuf_j, hj_le, hrpj_160,
                                hrpj_cap, hres_j, hmj⟩ ihj => by
                            rw [Blocks.get_here]
                            bve_jnz hj_lt
                            · bve_jnz hfit_j
                              · have hj_nat : j.toNat < nn.toNat := by
                                  rw [BitVec.ult, decide_eq_true_eq] at hj_lt; exact hj_lt
                                have hhj1 : (j + 1#32).toNat = j.toNat + 1 := by
                                  rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
                                    Nat.mod_eq_of_lt (by omega : j.toNat + 1 < 2 ^ 32)]
                                refine wp_join_group (ts := [i64, i64, .bool])
                                  (fun (rc_n, rp_n, _fit_n, _) mn =>
                                    ∃ sn,
                                      FullDenseInvW c F0 F_cur sn ∧
                                      sn.core.cur_vars = s2.core.cur_vars ∧
                                      sn.core.fuel = s2.core.fuel ∧
                                      sn.core.arena = s2.core.arena ∧
                                      sn.core.arena_len = s2.core.arena_len ∧
                                      (∀ idx < 96, sn.scratch.scratch_buf[idx]? = scr2[idx]?) ∧
                                      160 ≤ rp_n.toNat ∧ rp_n.toNat ≤ c.scratch_cap ∧
                                      FullResBufOkW F_cur sn rp_n.toNat 160 ∧
                                      (FullMem c sn ⋆ R) mn) ?_ ?_
                                · rintro Js2 ⟨rc_n, rp_n, _fit_n, ⟨⟩⟩ mn
                                    ⟨sn, hinvn, hcvn, hfln, harn, haln, hbuf_n, hrpn_160,
                                      hrpn_cap, hres_n, hmn⟩
                                  rw [Blocks.get_here]
                                  bve_jump
                                  exact ihj (rc_n, rp_n, j + 1#32, ()) mn
                                    (by dsimp only; rw [hhj1]; omega)
                                    ⟨sn, hinvn, hcvn, hfln, harn, haln, hbuf_n, by rw [hhj1]; omega,
                                      hrpn_160, hrpn_cap, hres_n, hmn⟩
                                · intro Js2 hJs2
                                  bve_jnz hmask
                                  · have hsj_len := hinvj.1.scratch_ok.scratch_buf_len
                                    have hi_eq : (i.setWidth 64).toNat = i.toNat := by
                                      rw [BitVec.toNat_setWidth,
                                        Nat.mod_eq_of_lt (by omega : i.toNat < 2 ^ 64)]
                                    have hi_sj :
                                        (i.setWidth 64).toNat < sj.scratch.scratch_buf.length := by
                                      omega
                                    have hj64_eq : ((64#32 + j).setWidth 64).toNat =
                                        64 + j.toNat := by
                                      rw [BitVec.toNat_setWidth, BitVec.toNat_add,
                                        show (64#32 : BitVec 32).toNat = 64 from rfl,
                                        Nat.mod_eq_of_lt (by omega : 64 + j.toNat < 2 ^ 32),
                                        Nat.mod_eq_of_lt (by omega : 64 + j.toNat < 2 ^ 64)]
                                    have hj64_sj : ((64#32 + j).setWidth 64).toNat <
                                        sj.scratch.scratch_buf.length := by omega
                                    bve_ld (c0_load_full_scratch_buf (i := i.setWidth 64)
                                      hi_sj hmj)
                                    bve_ld (c0_load_full_scratch_buf (i := (64#32 + j).setWidth 64)
                                      hj64_sj hmj)
                                    bve_lets
                                    have hwi_j :
                                        sj.scratch.scratch_buf[(i.setWidth 64).toNat]'hi_sj =
                                          scr2[i.toNat]?.getD 0#32 := by
                                      have h0 : sj.scratch.scratch_buf[i.toNat]? =
                                          some (sj.scratch.scratch_buf[(i.setWidth 64).toNat]'
                                            hi_sj) := by
                                        rw [← hi_eq, List.getElem?_eq_getElem hi_sj]
                                      have h1 := h0.symm.trans (hbuf_j i.toNat (by omega))
                                      rw [← h1]; rfl
                                    have hwj_j :
                                        sj.scratch.scratch_buf[((64#32 + j).setWidth 64).toNat]'
                                            hj64_sj =
                                          scr2[64 + j.toNat]?.getD 0#32 := by
                                      have h0 : sj.scratch.scratch_buf[64 + j.toNat]? =
                                          some (sj.scratch.scratch_buf[((64#32 + j).setWidth
                                            64).toNat]'hj64_sj) := by
                                        rw [← hj64_eq, List.getElem?_eq_getElem hj64_sj]
                                      have h1 := h0.symm.trans (hbuf_j (64 + j.toNat) (by omega))
                                      rw [← h1]; rfl
                                    refine wp_call_of_spec _ _ (hResolve _ _ _ X ?_)
                                    simp only [vals_nil, vals_cons, Arg.val_var]
                                    refine ⟨c, F0, F_cur, sj, R, rfl, hinvj,
                                      (by rw [hcvj, hs2_cv]; exact hv_lt),
                                      (by rw [hwi_j]
                                          exact FullBveEntryOkW.with_state
                                            (by rw [hcvj]; exact Nat.le_refl _) harj halj
                                            (hp_ok i.toNat hi_nat)),
                                      (by rw [hwj_j]
                                          exact FullBveEntryOkW.with_state
                                            (by rw [hcvj]; exact Nat.le_refl _) harj halj
                                            (hn_ok j.toNat hj_nat)),
                                      hmj, ?_⟩
                                    rintro ok_r lm' tmp' tl' m_r sr hinv_r htl_r hok_rt hm_r
                                    bve_jnz hok_r
                                    · obtain ⟨htl_lits, htl_nd, htl_ent⟩ := hok_rt hok_r
                                      bve_jnz hrc_ov
                                      · bve_jump
                                        exact hJs (rc_j + 1#64, rp_j, false, j, ()) m_r
                                          ⟨sr, hinv_r, hcvj, hflj, harj, halj, hbuf_j,
                                            (fun h => by cases h), hm_r⟩
                                      · bve_ld load_full_tmp_len hm_r
                                        bve_ld load_full_scratch_cap hm_r
                                        bve_jnz hrp_ov
                                        · bve_jump
                                          exact hJs (rc_j + 1#64, rp_j, false, j, ()) m_r
                                            ⟨sr, hinv_r, hcvj, hflj, harj, halj, hbuf_j,
                                              (fun h => by cases h), hm_r⟩
                                        · have htl_lt64 : tl' < 2 ^ 64 := by omega
                                          have htl_lt32 : tl' < 2 ^ 32 := by omega
                                          have hrp_sum_nat :
                                              (rp_j + 1#64 + BitVec.ofNat 64 tl').toNat =
                                                rp_j.toNat + 1 + tl' := by
                                            rw [BitVec.toNat_add, BitVec.toNat_add,
                                              show (1#64 : BitVec 64).toNat = 1 from rfl,
                                              BitVec.toNat_ofNat,
                                              Nat.mod_eq_of_lt htl_lt64,
                                              Nat.mod_eq_of_lt
                                                (by omega : rp_j.toNat + 1 < 2 ^ 64),
                                              Nat.mod_eq_of_lt
                                                (by omega : rp_j.toNat + 1 + tl' < 2 ^ 64)]
                                          have hrp_fit : rp_j.toNat + 1 + tl' ≤ c.scratch_cap := by
                                            change (BitVec.ofNat 64 c.scratch_cap).ult
                                                (rp_j + 1#64 + BitVec.ofNat 64 tl') =
                                              false at hrp_ov
                                            rw [BitVec.ult, decide_eq_false_iff_not,
                                              BitVec.toNat_ofNat,
                                              Nat.mod_eq_of_lt
                                                (by omega : c.scratch_cap < 2 ^ 64),
                                              hrp_sum_nat] at hrp_ov
                                            omega
                                          have hrp_lt_scr :
                                              rp_j.toNat < sr.scratch.scratch_buf.length := by
                                            rw [hinv_r.1.scratch_ok.scratch_buf_len]; omega
                                          bve_ld load_full_tmp_len hm_r
                                          bve_st m_len, hm_len :=
                                            c0_store_full_scratch_buf (i := rp_j)
                                              ((BitVec.ofNat 64 tl').setWidth 32)
                                              hrp_lt_scr hm_r
                                          let sk0 : FullState :=
                                            { sr with scratch :=
                                              { sr.scratch with scratch_buf :=
                                                  (sr.scratch.scratch_buf.set rp_j.toNat
                                                    ((BitVec.ofNat 64 tl').setWidth 32)) } }
                                          have hinv_k0 : FullDenseInvW c F0 F_cur sk0 :=
                                            FullDenseInvW.with_scratch_buf hinv_r
                                              (by rw [List.length_set]
                                                  exact hinv_r.1.scratch_ok.scratch_buf_len)
                                          bve_ld load_full_tmp_lits_ptr hm_len
                                          refine wp_loop_inv (ts := [i32])
                                            (fun (k, _) mk =>
                                              ∃ sk : FullState,
                                                FullDenseInvW c F0 F_cur sk ∧ sk.core = sr.core ∧
                                                k.toNat ≤ tl' ∧
                                                (∀ idx < 96,
                                                  sk.scratch.scratch_buf[idx]? = scr2[idx]?) ∧
                                                (∀ idx < rp_j.toNat,
                                                  sk.scratch.scratch_buf[idx]? =
                                                    sj.scratch.scratch_buf[idx]?) ∧
                                                (sk.scratch.scratch_buf[rp_j.toNat]?.getD
                                                  0#32).toNat = tl' ∧
                                                (∀ t < k.toNat,
                                                  sk.scratch.scratch_buf[rp_j.toNat + 1 + t]? =
                                                    tmp'[t]?) ∧
                                                (FullMem c sk ⋆ R) mk)
                                            (fun (k, _) _ => tl' - k.toNat)
                                            (fun Jk hJk => by
                                              bve_jump
                                              exact hJk (0#32, PUnit.unit) m_len
                                                ⟨sk0, hinv_k0, rfl, Nat.zero_le _,
                                                  (fun idx hi => by
                                                    dsimp only [sk0]
                                                    rw [List.getElem?_set_ne (by omega)]
                                                    exact hbuf_j idx hi),
                                                  (fun idx hi => by
                                                    dsimp only [sk0]
                                                    rw [List.getElem?_set_ne (by omega)]),
                                                  (by
                                                    dsimp only [sk0]
                                                    rw [List.getElem?_set_self hrp_lt_scr,
                                                      Option.getD_some, BitVec.toNat_setWidth,
                                                      BitVec.toNat_ofNat, Nat.mod_eq_of_lt htl_lt64,
                                                      Nat.mod_eq_of_lt htl_lt32]),
                                                  (fun _ ht => absurd ht (Nat.not_lt_zero _)),
                                                  hm_len⟩)
                                            (fun Jk ⟨k, ⟨⟩⟩ mk
                                                ⟨sk, hinv_k, hcore_k, hk_le, hbuf_k96, hbuf_krp,
                                                  hsz_k, hcp_k, hmk⟩ ihk => by
                                              rw [Blocks.get_here]
                                              bve_ld load_full_tmp_len hmk
                                              bve_jnz hk_lt
                                              · have hk_eq : (k.setWidth 64).toNat = k.toNat := by
                                                  rw [BitVec.toNat_setWidth,
                                                    Nat.mod_eq_of_lt
                                                      (by have := k.isLt; omega :
                                                        k.toNat < 2 ^ 64)]
                                                have hk_nat : k.toNat < tl' := by
                                                  have h0 : BitVec.ult (k.setWidth 64)
                                                      (BitVec.ofNat 64 sk.core.tmp_len) = true :=
                                                    hk_lt
                                                  rw [hcore_k] at h0
                                                  rw [BitVec.ult, decide_eq_true_eq, hk_eq,
                                                    BitVec.toNat_ofNat,
                                                    Nat.mod_eq_of_lt htl_lt64] at h0
                                                  exact h0
                                                have hk_tmp :
                                                    (k.setWidth 64).toNat < sk.core.tmp.length := by
                                                  rw [hk_eq, hinv_k.1.core_ok.tmp_len_arr]
                                                  exact Nat.lt_of_lt_of_le hk_nat
                                                    (Nat.le_trans htl_r (by
                                                      rw [hcvj]; exact hcv_le))
                                                have hk_scr_nat :
                                                    (rp_j + 1#64 + k.setWidth 64).toNat =
                                                      rp_j.toNat + 1 + k.toNat := by
                                                  rw [BitVec.toNat_add, BitVec.toNat_add,
                                                    show (1#64 : BitVec 64).toNat = 1 from rfl,
                                                    hk_eq,
                                                    Nat.mod_eq_of_lt
                                                      (by omega : rp_j.toNat + 1 < 2 ^ 64),
                                                    Nat.mod_eq_of_lt
                                                      (by omega :
                                                        rp_j.toNat + 1 + k.toNat < 2 ^ 64)]
                                                have hk_scr :
                                                    (rp_j + 1#64 + k.setWidth 64).toNat <
                                                      sk.scratch.scratch_buf.length := by
                                                  rw [hk_scr_nat,
                                                    hinv_k.1.scratch_ok.scratch_buf_len]
                                                  omega
                                                bve_ld (c0_load_full_tmp (i := k.setWidth 64)
                                                  hk_tmp hmk)
                                                bve_st m_k1, hm_k1 :=
                                                  c0_store_full_scratch_buf
                                                    (i := rp_j + 1#64 + k.setWidth 64)
                                                    (sk.core.tmp[(k.setWidth 64).toNat]'hk_tmp)
                                                    hk_scr hmk
                                                bve_jump
                                                let sk1 : FullState :=
                                                  { sk with scratch :=
                                                    { sk.scratch with scratch_buf :=
                                                        (sk.scratch.scratch_buf.set
                                                          (rp_j + 1#64 + k.setWidth 64).toNat
                                                          (sk.core.tmp[(k.setWidth 64).toNat]'
                                                            hk_tmp)) } }
                                                have hinv_k1 : FullDenseInvW c F0 F_cur sk1 :=
                                                  FullDenseInvW.with_scratch_buf hinv_k
                                                    (by rw [List.length_set]
                                                        exact hinv_k.1.scratch_ok.scratch_buf_len)
                                                have hk1 : (k + 1#32).toNat = k.toNat + 1 := by
                                                  rw [BitVec.toNat_add,
                                                    show (1#32 : BitVec 32).toNat = 1 from rfl,
                                                    Nat.mod_eq_of_lt
                                                      (by omega : k.toNat + 1 < 2 ^ 32)]
                                                have hval_k :
                                                    some (sk.core.tmp[(k.setWidth 64).toNat]'
                                                      hk_tmp) = tmp'[k.toNat]? := by
                                                  have htmpeq : sk.core.tmp = tmp' := by
                                                    rw [hcore_k]
                                                  exact Eq.symm (by
                                                    rw [← htmpeq, ← hk_eq,
                                                      List.getElem?_eq_getElem hk_tmp])
                                                exact ihk (k + 1#32, PUnit.unit) m_k1
                                                  (by dsimp only; rw [hk1]; omega)
                                                  ⟨sk1, hinv_k1, hcore_k, by rw [hk1]; omega,
                                                    (fun idx hi => by
                                                      dsimp only [sk1]
                                                      rw [List.getElem?_set_ne
                                                        (by rw [hk_scr_nat]; omega)]
                                                      exact hbuf_k96 idx hi),
                                                    (fun idx hi => by
                                                      dsimp only [sk1]
                                                      rw [List.getElem?_set_ne
                                                        (by rw [hk_scr_nat]; omega)]
                                                      exact hbuf_krp idx hi),
                                                    (by
                                                      dsimp only [sk1]
                                                      rw [List.getElem?_set_ne
                                                        (by rw [hk_scr_nat]; omega)]
                                                      exact hsz_k),
                                                    (fun t ht => by
                                                      rw [hk1] at ht; dsimp only [sk1]
                                                      rcases Nat.lt_or_eq_of_le
                                                          (Nat.lt_succ_iff.mp ht) with hlt | rfl
                                                      · rw [List.getElem?_set_ne
                                                          (by rw [hk_scr_nat]; omega)]
                                                        exact hcp_k t hlt
                                                      · rw [hk_scr_nat, List.getElem?_set_self (by
                                                          rw [← hk_scr_nat]; exact hk_scr)]
                                                        exact hval_k),
                                                    hm_k1⟩
                                              · have hk_eq_tl : k.toNat = tl' := by
                                                  have h0 : BitVec.ult (k.setWidth 64)
                                                      (BitVec.ofNat 64 sk.core.tmp_len) =
                                                      false := hk_lt
                                                  rw [hcore_k] at h0
                                                  rw [BitVec.ult, decide_eq_false_iff_not,
                                                    BitVec.toNat_setWidth,
                                                    Nat.mod_eq_of_lt (by
                                                      have := k.isLt; omega : k.toNat < 2 ^ 64),
                                                    BitVec.toNat_ofNat,
                                                    Nat.mod_eq_of_lt htl_lt64] at h0
                                                  omega
                                                bve_ld load_full_tmp_len hmk
                                                bve_jump
                                                have htmp_tl : tl' ≤ tmp'.length := by
                                                  have := hinv_k.1.core_ok.tmp_len_arr
                                                  rw [hcore_k] at this
                                                  change tmp'.length = c.max_vars at this
                                                  rw [this]
                                                  exact Nat.le_trans htl_r (by
                                                    rw [hcvj]; exact hcv_le)
                                                have hcv_sk : sk.core.cur_vars = s2.core.cur_vars :=
                                                  by rw [hcore_k]; exact hcvj
                                                have hfl_sk : sk.core.fuel = s2.core.fuel := by
                                                  rw [hcore_k]; exact hflj
                                                have har_sk : sk.core.arena = s2.core.arena := by
                                                  rw [hcore_k]; exact harj
                                                have hal_sk :
                                                    sk.core.arena_len = s2.core.arena_len := by
                                                  rw [hcore_k]; exact halj
                                                have hcp_tl : ∀ t < tl',
                                                    sk.scratch.scratch_buf[rp_j.toNat + 1 + t]? =
                                                      tmp'[t]? :=
                                                  fun t ht => hcp_k t (by omega)
                                                have hres_sk :
                                                    FullResBufOkW F_cur sk
                                                      (rp_j + 1#64 +
                                                        BitVec.ofNat 64 sk.core.tmp_len).toNat
                                                      160 := by
                                                  rw [hcore_k]
                                                  change FullResBufOkW F_cur sk
                                                    (rp_j + 1#64 + BitVec.ofNat 64 tl').toNat 160
                                                  rw [hrp_sum_nat]
                                                  refine FullResBufOkW.append_block
                                                    (s := sj) (s' := sk) (r0 := 160)
                                                    (r1 := rp_j.toNat) (sz := tl')
                                                    (by rw [hcore_k]) hbuf_krp hsz_k ?_ ?_ ?_
                                                    hres_j
                                                  · intro t ht
                                                    rw [hcp_tl t ht, hcore_k]
                                                    exact htl_lits t ht
                                                  · rw [range_map_div2_eq_take_map htmp_tl hcp_tl]
                                                    exact htl_nd
                                                  · rw [range_map_eq_take_map htmp_tl hcp_tl]
                                                    exact htl_ent
                                                exact hJs2 (rc_j + 1#64,
                                                    rp_j + 1#64 +
                                                      BitVec.ofNat 64 sk.core.tmp_len, fit_i, ())
                                                  mk
                                                  ⟨sk, hinv_k, hcv_sk, hfl_sk, har_sk, hal_sk,
                                                    hbuf_k96,
                                                    (by rw [hcore_k]
                                                        change 160 ≤
                                                          (rp_j + 1#64 +
                                                            BitVec.ofNat 64 tl').toNat
                                                        rw [hrp_sum_nat]; omega),
                                                    (by rw [hcore_k]
                                                        change (rp_j + 1#64 +
                                                            BitVec.ofNat 64 tl').toNat ≤
                                                          c.scratch_cap
                                                        rw [hrp_sum_nat]; omega),
                                                    hres_sk, hmk⟩)
                                    · bve_jump
                                      exact hJs2 (rc_j, rp_j, fit_i, ()) m_r
                                        ⟨sr, hinv_r, hcvj, hflj, harj, halj, hbuf_j, hrpj_160,
                                          hrpj_cap,
                                          FullResBufOkW.with_state (s := sj) (s' := sr) rfl
                                            (fun _ _ => rfl) hres_j,
                                          hm_r⟩
                                  · bve_jump
                                    exact hJs2 (rc_j, rp_j, fit_i, ()) mj
                                      ⟨sj, hinvj, hcvj, hflj, harj, halj, hbuf_j, hrpj_160,
                                        hrpj_cap, hres_j, hmj⟩
                              · exact absurd hfit_j (by rw [hfit_i]; decide)
                            · bve_jump
                              exact hJs (rc_j, rp_j, fit_i, j, ()) mj
                                ⟨sj, hinvj, hcvj, hflj, harj, halj, hbuf_j,
                                  (fun _ => ⟨hrpj_160, hrpj_cap, hres_j⟩), hmj⟩)
                    · bve_jump
                      exact hJ_fit (rc, rp, fit_i, ()) ml
                        ⟨sf, hinvf, hcvf, hflf, harf, half, hbuf_f, hres_f, hml⟩
                  · bve_jump
                    exact hJ_fit (rc, rp, fit_i, ()) ml
                      ⟨sf, hinvf, hcvf, hflf, harf, half, hbuf_f, hres_f, hml⟩)
            · bve_jump; rw [hfit0]; exact hJ_fit (0#64, 160#64, false, PUnit.unit) m2
                ⟨s2, hinv2, rfl, rfl, rfl, rfl, (fun _ _ => rfl),
                  (fun h => by cases h), hm2⟩
        · intro J hJ
          bve_jnz hext
          · -- ext_ok = true
            refine wp_join_group (ts := []) (fun _ ml =>
                (np = 0#32 ∨ nn = 0#32) ∧ ml = m2) ?_ ?_
            · rintro J1 _ ml ⟨hzero, h_ml⟩; subst ml
              rw [Blocks.get_here]
              bve_lets
              refine wp_join_group (ts := []) (fun _ ml =>
                  ∃ sw, FullDenseInvW c F0 F_cur sw ∧ sw.core.cur_vars = s.core.cur_vars ∧
                    sw.core.fuel = s.core.fuel ∧ (FullMem c sw ⋆ R) ml) ?_ ?_
              · rintro J_oom _ ml ⟨sw, hinvw, hcvw, hflw, hmw⟩
                rw [Blocks.get_here]
                bve_st ml1, hm_oom := store_full_oom 1#64 hmw
                bve_ret
                exact hQ 2#64 _ ml1 (FullDenseInvW.with_oom hinvw 1#64).toDense
                  (by rw [← hcvw]; exact Nat.le_refl _) (by rw [← hflw]; exact Nat.le_refl _)
                  (Or.inr (Or.inl rfl)) (fun h => by cases h) hm_oom
              · intro J_oom hJ_oom
                refine wp_join_group (ts := []) (fun _ ml =>
                    ∃ sw, FullDenseInvW c F0 F_cur sw ∧ sw.core.cur_vars = s.core.cur_vars ∧
                      sw.core.fuel = s.core.fuel ∧
                      fullArenaClauseRefs sw = fullArenaClauseRefs s2 ∧
                      sw.scratch.scratch_buf = scr2 ∧ (FullMem c sw ⋆ R) ml) ?_ ?_
                · rintro J_nn _ ml ⟨sw, hinvw, hcvw, hflw, hrefs_sw, hscr_sw, hmw⟩
                  rw [Blocks.get_here]
                  refine wp_join_group (ts := []) (fun _ ml =>
                      ∃ sw1, FullDenseInvW c F0 F_cur sw1 ∧ sw1.core.cur_vars = s.core.cur_vars ∧
                        sw1.core.fuel = s.core.fuel ∧ (FullMem c sw1 ⋆ R) ml) ?_ ?_
                  · rintro J_inact _ ml1 ⟨sw1, hinvw1, hcvw1, hflw1, hmw1⟩
                    rw [Blocks.get_here]
                    bve_lets
                    refine wp_call_of_spec _ _ (hSetInact _ _ _ X ?_)
                    simp only [vals_nil, vals_cons, Arg.val_var]
                    refine ⟨c, sw1, R, rfl, hinvw1.1, hmw1, ?_⟩
                    intro flags' unass' m_si hfl_len hm_si
                    let sw2 : FullState :=
                      { sw1 with core := { sw1.core with flags := flags', unassigned := unass' } }
                    have hinvw2 := FullDenseInvW.with_flags_unassigned hinvw1 hfl_len unass'
                    bve_ld load_full_bve_cnt hm_si
                    bve_st ml_bve, hm_bve := store_full_bve_cnt (sw2.scratch.bve_cnt + 1#64) hm_si
                    bve_ret
                    exact hQ 1#64 _ ml_bve (FullDenseInvW.with_bve_cnt hinvw2 _).toDense
                      (by rw [← hcvw1]; exact Nat.le_refl _) (by rw [← hflw1]; exact Nat.le_refl _)
                      (Or.inl rfl) (fun h => by cases h) hm_bve
                  · intro J_inact hJ_inact
                    bve_jnz hnn_pos
                    · refine wp_call_of_spec _ _ (hWeaken _ _ _ X ?_)
                      simp only [vals_nil, vals_cons, Arg.val_var, Arg.val_imm]
                      refine ⟨c, F0, F_cur, sw, R, rfl, hinvw,
                        (by change (pl ||| 1#32).toNat < 2 * sw.core.cur_vars
                            rw [hnl_nat, hcvw, hs2_cv]; omega),
                        (by rw [h64_32]; omega),
                        (fun j hj => by
                          rw [hscr_sw, h64_32]
                          exact fullBveWeakItemOk_of_pres hcvw hrefs_sw
                            (FullBveEntryOkW.to_weak (hn_ok j hj))),
                        hmw, ?_⟩
                      intro ok2 sw' m_w2 hinvw' hcvw' hflw' hscr_w2 hrefs_w2 hm_w2
                      bve_jnz hok2
                      · bve_jump; exact hJ_inact () m_w2 ⟨sw', hinvw', hcvw'.trans hcvw,
                          hflw'.trans hflw, hm_w2⟩
                      · bve_jump; exact hJ_oom () m_w2 ⟨sw', hinvw', hcvw'.trans hcvw,
                          hflw'.trans hflw, hm_w2⟩
                    · bve_jump; exact hJ_inact () ml ⟨sw, hinvw, hcvw, hflw, hmw⟩
                · intro J_nn hJ_nn
                  bve_jnz hnp_pos
                  · refine wp_call_of_spec _ _ (hWeaken _ _ _ X ?_)
                    simp only [vals_nil, vals_cons, Arg.val_var, Arg.val_imm]
                    refine ⟨c, F0, F_cur, s2, R, rfl, hinv2,
                      (by change pl.toNat < 2 * s2.core.cur_vars; rw [hpl_nat, hs2_cv]; omega),
                      (by rw [h0_32]; omega),
                      (fun i hi => by
                        rw [h0_32, Nat.zero_add]
                        exact FullBveEntryOkW.to_weak (hp_ok i hi)),
                      hm2, ?_⟩
                    intro ok1 s2' m_w1 hinvw1 hcv1 hfl1 hscr_w1 hrefs_w1 hm_w1
                    bve_jnz hok1
                    · bve_jump; exact hJ_nn () m_w1 ⟨s2', hinvw1, hcv1, hfl1, hrefs_w1,
                        hscr_w1, hm_w1⟩
                    · bve_jump; exact hJ_oom () m_w1 ⟨s2', hinvw1, hcv1, hfl1, hm_w1⟩
                  · bve_jump; exact hJ_nn () m2 ⟨s2, hinv2, rfl, rfl, rfl, rfl, hm2⟩
            · intro J1 hJ1
              bve_jnz hnp0
              · bve_jump; exact hJ1 () m2 ⟨Or.inl (by simpa using hnp0), rfl⟩
              · bve_jnz hnn0
                · bve_jump; exact hJ1 () m2 ⟨Or.inr (by simpa using hnn0), rfl⟩
                · bve_jump; exact hJ () m2 rfl
          · bve_jump; exact hJ () m2 rfl

end

end LeanQbe.T.Examples.Kissat.Full
