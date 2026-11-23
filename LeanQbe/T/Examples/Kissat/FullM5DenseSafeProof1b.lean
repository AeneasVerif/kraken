module

public import LeanQbe.T.Examples.Kissat.FullM5DenseSafe
public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.FullFastBveBudgetsLemmas1
import LeanQbe.T.Examples.Kissat.FullBveVarLemmas2

/-!
# Kissat M5 Dense-Safe Proofs — Part 1b (`full_bve_var_m5`)

Proves `full_bve_var_m5_wp` (`Full.fullBveVarSpec`) and `full_bve_var_m5_def_wp`
(`FullFastBveBudgets.fullBveVarDefSpec`) with OOM watch-headroom pre-checks:
1. Returns `2ULL` immediately if `h->oom != 0ULL` on entry.
2. Pre-checks worst-case `watch_stk` headroom across all buffered resolvents (calling
   `full_wstack_defrag` if needed) **BEFORE** calling `full_bve_weaken` or marking `FL_ELIM`,
   aborting cleanly to the BCE fallback when `watch_stk` headroom is insufficient.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullM5DenseSafe

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullBveVarTactics
open LeanQbe.T.Examples.Kissat.Full.FullBveVarHelpers
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open Kraken.Bedrock2.Test
open scoped FullArenaTactics FullBveVarTactics

/-! ## 1. Local Stepping Macros & Defrag / ResBuf Helpers -/

section BveVarHelpers

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
private theorem bl_not_bool {Γ} {rs : List Ty} {Q : Post rs} {X} {a : Arg Val .bool} {k m} :
    wp Γ Q X (.let_ (Op.mk (.not .bool) (a, ())) k) m =
      wp Γ Q X (k (!a.val, ())) m := by simp [wp_let_not_eq, lift1]
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
private theorem bl_uge32 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i32} {h} {k m} :
    wp Γ Q X (.let_ (Op.mk (.cmp .uge i32 .bool h) (a, b, ())) k) m =
      wp Γ Q X (k (b.val.ule a.val, ())) m := by simp [wp_let_cmp_eq, liftCmp, evalBits_uge_eq]
private theorem bl_ult64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i64} {h} {k m} :
    wp Γ Q X (.let_ (Op.mk (.cmp .ult i64 .bool h) (a, b, ())) k) m =
      wp Γ Q X (k (a.val.ult b.val, ())) m := by simp [wp_let_cmp_eq, liftCmp, evalBits_ult_eq]
private theorem bl_ule64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i64} {h} {k m} :
    wp Γ Q X (.let_ (Op.mk (.cmp .ule i64 .bool h) (a, b, ())) k) m =
      wp Γ Q X (k (a.val.ule b.val, ())) m := by simp [wp_let_cmp_eq, liftCmp, evalBits_ule_eq]
private theorem bl_ugt64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i64} {h} {k m} :
    wp Γ Q X (.let_ (Op.mk (.cmp .ugt i64 .bool h) (a, b, ())) k) m =
      wp Γ Q X (k (b.val.ult a.val, ())) m := by simp [wp_let_cmp_eq, liftCmp, evalBits_ugt_eq]
private theorem bl_uge64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i64} {h} {k m} :
    wp Γ Q X (.let_ (Op.mk (.cmp .uge i64 .bool h) (a, b, ())) k) m =
      wp Γ Q X (k (b.val.ule a.val, ())) m := by simp [wp_let_cmp_eq, liftCmp, evalBits_uge_eq]
private theorem bl_eq32 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i32} {h} {k m} :
    wp Γ Q X (.let_ (Op.mk (.cmp .eq i32 .bool h) (a, b, ())) k) m =
      wp Γ Q X (k (a.val == b.val, ())) m := by simp [wp_let_cmp_eq, liftCmp, evalBits_eq_beq]
private theorem bl_ne32 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i32} {h} {k m} :
    wp Γ Q X (.let_ (Op.mk (.cmp .ne i32 .bool h) (a, b, ())) k) m =
      wp Γ Q X (k (a.val != b.val, ())) m := by simp [wp_let_cmp_eq, liftCmp, evalBits_ne_bne]
private theorem bl_eq64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i64} {h} {k m} :
    wp Γ Q X (.let_ (Op.mk (.cmp .eq i64 .bool h) (a, b, ())) k) m =
      wp Γ Q X (k (a.val == b.val, ())) m := by simp [wp_let_cmp_eq, liftCmp, evalBits_eq_beq]
private theorem bl_ne64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i64} {h} {k m} :
    wp Γ Q X (.let_ (Op.mk (.cmp .ne i64 .bool h) (a, b, ())) k) m =
      wp Γ Q X (k (a.val != b.val, ())) m := by simp [wp_let_cmp_eq, liftCmp, evalBits_ne_bne]
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
        | rw [bl_and32] | rw [bl_and64] | rw [bl_or32] | rw [bl_or64] | rw [bl_not_bool]
        | rw [bl_zext32_64] | rw [bl_sext32_64] | rw [bl_trunc64_32]
        | rw [bl_ult32] | rw [bl_ugt32] | rw [bl_uge32]
        | rw [bl_ult64] | rw [bl_ule64] | rw [bl_ugt64] | rw [bl_uge64]
        | rw [bl_eq32] | rw [bl_ne32] | rw [bl_eq64] | rw [bl_ne64]
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

private theorem bve_resBuf_of_bve {F_cur : List (List Nat)} {s : FullState} {r_end p : Nat}
    (h : FullBveVarSpecs.FullResBufOkW F_cur s r_end p) : FullResBufOkW F_cur s r_end p := by
  induction h with
  | nil => exact .nil
  | cons hbd hsz hlts hnd hent _ ih => exact .cons hbd hsz hlts hnd hent ih

private theorem bve_resBuf_head {F_cur : List (List Nat)} {s : FullState} {r_end p : Nat}
    (hres : FullBveVarSpecs.FullResBufOkW F_cur s r_end p) (hlt : p < r_end) :
    p + 1 + (s.scratch.scratch_buf[p]?.getD 0#32).toNat ≤ r_end ∧
      let sz := (s.scratch.scratch_buf[p]?.getD 0#32).toNat
      (∀ k < sz, (s.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
      FullBveVarSpecs.FullResBufOkW F_cur s r_end (p + 1 + sz) := by
  cases hres with
  | nil => exact absurd hlt (Nat.lt_irrefl _)
  | @cons _ sz0 hbd hsz hlts _ _ htail =>
    subst hsz; exact ⟨hbd, hlts, htail⟩

private theorem denseWatchSliceOk_congr {F_cur : List (List Nat)} {k k' : FullCoreState}
    {l off off' n : Nat} (hcv : k'.cur_vars = k.cur_vars)
    (hrefs : fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k)
    (hw : ∀ j < n, k'.wstk[off' + j]? = k.wstk[off + j]?)
    (h : DenseWatchSliceOk F_cur k l off n) : DenseWatchSliceOk F_cur k' l off' n := by
  induction h generalizing off' with
  | empty => exact .empty
  | @bin p rem w0 hp hflag hne hlt hent _ ih =>
    exact .bin (by simpa using (hw 0 (Nat.zero_lt_succ _)).trans hp) hflag hne (by omega) hent
      (ih fun j hj => by simpa [Nat.add_assoc, Nat.add_comm 1 j] using hw (j + 1) (by omega))
  | @occ p rem w0 cref hp hp1 hflag h3 hlt href _ ih =>
    exact .occ (by simpa using (hw 0 (by omega)).trans hp) ((hw 1 (by omega)).trans hp1)
      hflag h3 hlt (by rwa [hrefs])
      (ih fun j hj => by simpa [Nat.add_assoc, Nat.add_comm 2 j] using hw (j + 2) (by omega))

private theorem bveDenseInvW_of_defrag {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hinv : FullBveVarSpecs.FullDenseInvW c F0 F_cur s)
    {wvec' wstk' wsort' : List (BitVec 32)} {wlen' : Nat}
    (hlen' : ({ s with
      core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 }
      scratch := { s.scratch with wsort := wsort' } } : FullState).LengthsOk c)
    (hlay' : WatchStackLayout
      { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 })
    (hsl : ∀ l < 2 * s.core.cur_vars,
      fullWatchSizeCore { s.core with wvec := wvec', wstk := wstk', wlen := wlen',
                                      wusable := 0#64 } l = fullWatchSizeCore s.core l ∧
      ∀ k < fullWatchSizeCore s.core l,
        wstk'[fullWatchOffCore { s.core with wvec := wvec', wstk := wstk', wlen := wlen',
                                             wusable := 0#64 } l + k]? =
        s.core.wstk[fullWatchOffCore s.core l + k]?) :
    FullBveVarSpecs.FullDenseInvW c F0 F_cur
      { s with
        core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 }
        scratch := { s.scratch with wsort := wsort' } } := by
  have hdm := hinv.2.2.2.2.2.2
  have hdw : DenseWatchesInv F_cur s.core := by
    have h := hinv.2.1.watches; unfold ModeWatchesInv at h; rwa [ite_eq_right hdm] at h
  let k' : FullCoreState :=
    { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 }
  have hdw' : DenseWatchesInv F_cur k' :=
    DenseWatchesInv.of_slices hlay'.bounds hlay'.pos_off hlay'.disjoint fun l hl => by
      obtain ⟨hsz, hget⟩ := hsl l hl
      rw [hsz]
      exact denseWatchSliceOk_congr (k := s.core) (k' := k') rfl rfl (fun j hj => hget j hj)
        (hdw.slices l hl)
  refine ⟨hlen', { hinv.2.1 with
    arena := { hinv.2.1.arena with len_ok := hinv.2.1.arena.len_ok }
    watches := by unfold ModeWatchesInv; rw [ite_eq_right hdm]; exact hdw' },
    hinv.2.2.1, hinv.2.2.2.1, hinv.2.2.2.2.1, hinv.2.2.2.2.2.1, hdm⟩

private theorem bve_setInact_adapter {Γ : Env}
    (hSetInact : ∀ a m Q X, fullSetInactiveSpec a m Q X →
      Γ "full_set_inactive" [i64, i32, i32] [] a m Q X) :
    ∀ a m Q X, FullBveVarSpecs.fullSetInactiveSpec a m Q X →
      Γ "full_set_inactive" [i64, i32, i32] [] a m Q X := by
  rintro ⟨h, v, flag, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  refine hSetInact _ m Q X ⟨c, s, R, rfl, hlen, hm, ?_⟩
  split
  · exact hQ s.core.flags s.core.unassigned m hlen.core_ok.flags_len hm
  · exact hQ

private theorem bve_tryBce_adapter {Γ : Env}
    (hTryBce : ∀ a m Q X, fullBveTryBceSpec a m Q X →
      Γ "full_bve_try_bce" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, FullBveVarSpecs.fullBveTryBceSpec a m Q X →
      Γ "full_bve_try_bce" [i64, i32, i32, i32, i32] [.bool] a m Q X := by
  rintro ⟨h, blk_lit, cr, opp_off, opp_n, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hdense, hblk, hcr, hoff, hopp, hm, hQ⟩
  have hcr_w : FullBveBceWeakOk c s cr := by
    unfold FullBveBceWeakOk; unfold FullBveVarSpecs.FullBveTryBceEntryOk at hcr
    by_cases hmsb : (cr &&& 0x80000000#32) ≠ 0#32
    · rw [ite_eq_left hmsb] at hcr ⊢; exact hcr
    · rw [ite_eq_right hmsb] at hcr ⊢; exact ⟨hcr.1, hcr.2.1, hcr.2.2.1⟩
  have hcr_nd : (cr &&& 0x80000000#32) = 0#32 →
      ((fullArenaClauseLits s cr.toNat).map (· / 2)).Nodup := by
    intro h0; unfold FullBveVarSpecs.FullBveTryBceEntryOk at hcr
    rw [ite_eq_right (Classical.not_not.mpr h0)] at hcr; exact hcr.2.2.2
  exact hTryBce _ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hdense, hblk, hcr_w, hcr_nd, hoff, hopp, hm, hQ⟩

private def BveBceStepInv (TmkInv : FullState → Prop) (c : FullCfg) (F0 : CNF Nat)
    (F_cur : List (List Nat)) (s : FullState) (scr2 : List (BitVec 32))
    (np nn : BitVec 32) (R : Mem 64 → Prop) (sn : FullState) (mn : Mem 64) : Prop :=
  FullBveVarSpecs.FullDenseInvW c F0 F_cur sn ∧ TmkInv sn ∧
  sn.core.cur_vars = s.core.cur_vars ∧ sn.core.fuel.toNat ≤ s.core.fuel.toNat ∧
  (∀ idx < 128, sn.scratch.scratch_buf[idx]? = scr2[idx]?) ∧
  (∀ k < np.toNat, FullBveVarSpecs.FullBveTryBceEntryOk c sn (scr2[k]?.getD 0#32)) ∧
  (∀ j < nn.toNat, FullBveVarSpecs.FullBveTryBceOppOk c sn (scr2[64 + j]?.getD 0#32)) ∧
  (FullMem c sn ⋆ R) mn

private def bDummyVal : (t : Ty) → Val t
  | .bits _ => 0 | .bool => true | .float _ => 0 | .pair a b => (bDummyVal a, bDummyVal b)
private def bDummyTup : (ts : List Ty) → Tup Val ts
  | [] => () | t :: ts => (bDummyVal t, bDummyTup ts)
private def bStep {rs : List Ty} : Expr Val Cont rs → Expr Val Cont rs
  | .let_ (ts := ts) _ k => k (bDummyTup ts) | .load t _ k => k (bDummyVal t)
  | .store _ _ k => k | .call (bs := bs) _ _ k => k (bDummyTup bs)
  | _ => .hlt
private def bSteps {rs : List Ty} : Nat → Expr Val Cont rs → Expr Val Cont rs
  | 0, e => e | n + 1, e => bSteps n (bStep e)
private def bLd64 {rs : List Ty} (v : Val i64) : Expr Val Cont rs → Expr Val Cont rs
  | .load (.bits 64) _ k => k v | _ => .hlt
private def bLet32 {rs : List Ty} (v : Val i32) : Expr Val Cont rs → Expr Val Cont rs
  | .let_ (ts := [.bits 32]) _ k => k (v, ()) | _ => .hlt
private def bCall32 {rs : List Ty} (v : Val i32) : Expr Val Cont rs → Expr Val Cont rs
  | .call (bs := [.bits 32]) _ _ k => k (v, ()) | _ => .hlt
private def bElse {rs : List Ty} : Expr Val Cont rs → Expr Val Cont rs
  | .jnz _ _ e => e | _ => .hlt
private def bGrp0 {rs : List Ty} (J : Cont []) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[]]) bs _ => (match bs (J, ()) with | .cons f .nil => f ()) | _ => .hlt
private def bGrpFit {rs : List Ty} (J : Cont [i64, i64, .bool]) :
    Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 64, .bits 64, .bool]]) bs _ =>
      (match bs (J, ()) with | .cons f .nil => f (0#64, 0#64, false, ())) | _ => .hlt

private theorem bve_bce_ext_post {TmkInv : FullState → Prop} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s stb se2 : FullState} {scr2 : List (BitVec 32)} {np nn : BitVec 32}
    (hinv_tb : FullBveVarSpecs.FullDenseInvW c F0 F_cur stb)
    (hcvl : stb.core.cur_vars = s.core.cur_vars) (hfll : stb.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hbuf_l : ∀ idx < 128, stb.scratch.scratch_buf[idx]? = scr2[idx]?)
    (htb_p : ∀ k < np.toNat, FullBveVarSpecs.FullBveTryBceEntryOk c stb (scr2[k]?.getD 0#32))
    (htb_n : ∀ j < nn.toNat, FullBveVarSpecs.FullBveTryBceOppOk c stb (scr2[64 + j]?.getD 0#32))
    (hcore_e2 : PreservesCoreSlice (fullSafetySlice c).coreProj stb se2)
    (hlen_e2 : se2.LengthsOk c) (hll_e2 : se2.scratch.last_learned = stb.scratch.last_learned)
    (hext_e2 : se2.scratch.extend_len ≤ c.extend_cap)
    (hscr_e2 : se2.scratch.scratch_buf = stb.scratch.scratch_buf)
    (htmk_e2 : TmkInv se2) {m_e2 : Mem 64} {R : Mem 64 → Prop}
    (hm_e2 : (FullMem c se2 ⋆ R) m_e2) :
    BveBceStepInv TmkInv c F0 F_cur s scr2 np nn R se2 m_e2 := by
  have heq_e2 : se2.core = stb.core := fullCoreState_agrees_with_scratch hcore_e2
  have hpres := full_bve_tryBce_pres (s := stb) (s' := se2)
    (congrArg FullCoreState.arena heq_e2) (congrArg FullCoreState.arena_len heq_e2) htb_p htb_n
  exact ⟨denseInvW_of_extPush hinv_tb hlen_e2 hcore_e2 hll_e2 hext_e2, htmk_e2,
    by rw [heq_e2]; exact hcvl, by rw [heq_e2]; exact hfll,
    fun idx hi => by rw [hscr_e2]; exact hbuf_l idx hi, hpres.1, hpres.2, hm_e2⟩

private theorem bve_bce_markGarb_post {TmkInv : FullState → Prop}
    (hTmk_cong : ∀ {s s' : FullState}, TmkInv s → s'.core.cur_vars = s.core.cur_vars →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark → TmkInv s')
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s se2 : FullState}
    {scr2 : List (BitVec 32)} {np nn : BitVec 32} {R : Mem 64 → Prop} {m_bce1 : Mem 64}
    {ccr : BitVec 32} (hstep : BveBceStepInv TmkInv c F0 F_cur s scr2 np nn R se2 m_bce1 → True)
    (hinv_e2 : FullBveVarSpecs.FullDenseInvW c F0 F_cur se2) (htmk_e2 : TmkInv se2)
    (hcv_e2 : se2.core.cur_vars = s.core.cur_vars)
    (hfl_e2 : se2.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hbuf_e2 : ∀ idx < 128, se2.scratch.scratch_buf[idx]? = scr2[idx]?)
    (he2_p : ∀ k < np.toNat, FullBveVarSpecs.FullBveTryBceEntryOk c se2 (scr2[k]?.getD 0#32))
    (he2_n : ∀ j < nn.toNat, FullBveVarSpecs.FullBveTryBceOppOk c se2 (scr2[64 + j]?.getD 0#32))
    (hcref : ccr.toNat ∈ fullArenaClauseRefs se2) (ag_mg : BitVec 64)
    (hm_bce1 : (FullMem c { se2 with
        core := { se2.core with
          arena := se2.core.arena.set ccr.toNat (fullArenaHdr se2 ccr.toNat ||| 0x00080000#32)
          arena_garbage := ag_mg }
        scratch := { se2.scratch with bce_cnt := se2.scratch.bce_cnt + 1#64 } } ⋆ R) m_bce1) :
    ∃ smg, BveBceStepInv TmkInv c F0 F_cur s scr2 np nn R smg m_bce1 := by
  let _ := hstep
  let ar_mg := se2.core.arena.set ccr.toNat (fullArenaHdr se2 ccr.toNat ||| 0x00080000#32)
  let smg : FullState :=
    { se2 with
      core := { se2.core with arena := ar_mg, arena_garbage := ag_mg }
      scratch := { se2.scratch with bce_cnt := se2.scratch.bce_cnt + 1#64 } }
  have hinv_mg := FullBveVarHelpers.FullDenseInvW.with_bce_cnt
    (FullBveVarHelpers.FullDenseInvW.of_markGarb_zero hinv_e2 hcref ag_mg)
    (se2.scratch.bce_cnt + 1#64)
  have htbe := full_bve_tryBce_of_markGarb hinv_e2.1 hinv_e2.2.1 hcref ag_mg he2_p he2_n
  have hpr := full_bve_tryBce_pres (s' := smg) rfl rfl htbe.1 htbe.2
  exact ⟨smg, hinv_mg, hTmk_cong htmk_e2 rfl rfl, hcv_e2, hfl_e2, hbuf_e2, hpr.1, hpr.2, hm_bce1⟩

private def m5BveBceLoopExpr (h pScr : Val i64) (v pl np nn : Val i32) : Expr Val Cont [i64] :=
  full_bve_var_m5_body Val Cont (h, v, ())
    |> bStep |> bLd64 0#64 |> bStep |> bElse
    |> bStep |> bLd64 0#64 |> bStep |> bElse
    |> bStep |> bLd64 pScr
    |> bLet32 pl |> bStep |> bCall32 np
    |> bSteps 3 |> bCall32 nn
    |> bStep |> bElse |> bStep |> bElse
    |> bSteps 9
    |> bGrp0 (fun _ _ => True) |> bSteps 6
    |> bGrpFit (fun _ _ => True)
    |> bGrp0 (fun _ _ => True)

private theorem m5_bve_bce_loop_wp (Γ : Env) (TmkInv : FullState → Prop)
    (hTmk_cong : ∀ {s s' : FullState}, TmkInv s → s'.core.cur_vars = s.core.cur_vars →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark → TmkInv s')
    (hTryBce : ∀ xs m Q X, FullBveVarSpecs.fullBveTryBceSpec xs m Q X →
      Γ "full_bve_try_bce" [i64, i32, i32, i32, i32] [.bool] xs m Q X)
    (hExtPush2 : ∀ (h : BitVec 64) (blk ot : BitVec 32) m Q X,
      (∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
        (h = c.hdr ∧ s.scratch.extend_len ≤ c.extend_cap) ∧ s.LengthsOk c ∧ TmkInv s ∧
        (FullMem c s ⋆ R) m ∧
        ∀ (r : Tup Val [.bool]) s' m',
          PreservesCoreSlice (fullSafetySlice c).coreProj s s' → s'.LengthsOk c →
          (s'.scratch.last_learned = s.scratch.last_learned ∧
           s'.scratch.extend_len ≤ c.extend_cap ∧
           s'.scratch.scratch_buf = s.scratch.scratch_buf) →
          TmkInv s' → (FullMem c s' ⋆ R) m' → Q r m') →
      Γ "full_extend_push2" [i64, i32, i32] [.bool] (h, blk, ot, ()) m Q X)
    (hDelBin : ∀ xs m Q X, FullBveVarSpecs.fullDeleteBinarySpec xs m Q X →
      Γ "full_delete_binary" [i64, i32, i32] [] xs m Q X)
    (hExtPushCl : ∀ (h : BitVec 64) (blk cr : BitVec 32) m Q X,
      (∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
        (h = c.hdr ∧ s.scratch.extend_len ≤ c.extend_cap) ∧ s.LengthsOk c ∧ TmkInv s ∧
        (FullMem c s ⋆ R) m ∧
        ∀ (r : Tup Val [.bool]) s' m',
          PreservesCoreSlice (fullSafetySlice c).coreProj s s' → s'.LengthsOk c →
          (s'.scratch.last_learned = s.scratch.last_learned ∧
           s'.scratch.extend_len ≤ c.extend_cap ∧
           s'.scratch.scratch_buf = s.scratch.scratch_buf) →
          TmkInv s' → (FullMem c s' ⋆ R) m' → Q r m') →
      Γ "full_extend_push_cl" [i64, i32, i32] [.bool] (h, blk, cr, ()) m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s sb : FullState}
    {scr2 : List (BitVec 32)} {R : Mem 64 → Prop} {v pl np nn : BitVec 32} {m_bce : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hv_lt : v.toNat < s.core.cur_vars) (hpl_nat : pl.toNat = 2 * v.toNat)
    (hnp_le : np.toNat ≤ 64) (hnn_le : nn.toNat ≤ 64) (hsc512 : 512 ≤ c.scratch_cap)
    (hinvb : FullBveVarSpecs.FullDenseInvW c F0 F_cur sb) (htmkb : TmkInv sb)
    (hcvb : sb.core.cur_vars = s.core.cur_vars) (hflb : sb.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hbuf_b : ∀ idx < 128, sb.scratch.scratch_buf[idx]? = scr2[idx]?)
    (hpbce : ∀ i < np.toNat, FullBveVarSpecs.FullBveTryBceEntryOk c sb (scr2[i]?.getD 0#32))
    (hnbce : ∀ j < nn.toNat, FullBveVarSpecs.FullBveTryBceOppOk c sb (scr2[64 + j]?.getD 0#32))
    (hmb : (FullMem c sb ⋆ R) m_bce)
    (hQ : ∀ r s' m',
      FullBveVarSpecs.FullDenseInv c F0 s' → TmkInv s' →
      s.core.cur_vars ≤ s'.core.cur_vars → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    wp Γ Q X (m5BveBceLoopExpr c.hdr c.pScratchBuf v pl np nn) m_bce := by
  have hmv := c.hmaxv; have harc := c.harena; have hsc := c.hscr
  unfold dimacsBound at hmv harc hsc
  have h64_32 : (64 : BitVec 32).toNat = 64 := rfl
  dsimp only [m5BveBceLoopExpr, bSteps, bStep, bLd64, bLet32, bCall32, bElse, bGrp0, bGrpFit,
    bDummyTup, bDummyVal, i64, i32, full_bve_var_m5_body]
  refine wp_loop_inv (ts := [i32])
    (fun (i, _) ml => ∃ sl, i.toNat ≤ np.toNat ∧
      BveBceStepInv TmkInv c F0 F_cur s scr2 np nn R sl ml)
    (fun (i, _) _ => np.toNat - i.toNat)
    (fun Jlp hJlp => by
      bve_jump
      exact hJlp (0#32, PUnit.unit) m_bce ⟨sb, Nat.zero_le _, hinvb, htmkb,
        hcvb, hflb, hbuf_b, hpbce, hnbce, hmb⟩)
    (fun Jlp ⟨i, ⟨⟩⟩ ml
        ⟨sl, hi_le, hinvl, htmkl, hcvl, hfll, hbuf_l, hpk, hnj, hml⟩ ihlp => by
      rw [Blocks.get_here]; bve_jnz hi_lt
      · have hi_nat : i.toNat < np.toNat := by
          rw [BitVec.ult, decide_eq_true_eq] at hi_lt; exact hi_lt
        have hscrl := hinvl.1.scratch_ok.scratch_buf_len
        have hi_eq : (i.setWidth 64).toNat = i.toNat := by
          rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : i.toNat < 2 ^ 64)]
        have hi_scr : (i.setWidth 64).toNat < sl.scratch.scratch_buf.length := by omega
        have hwi_eq : sl.scratch.scratch_buf[i.toNat]'(by omega) =
            scr2[i.toNat]?.getD 0#32 := by
          have := hbuf_l i.toNat (by omega)
          rw [List.getElem?_eq_getElem
            (by omega : i.toNat < sl.scratch.scratch_buf.length)] at this
          rw [← this]; rfl
        refine wp_join_group (ts := [])
          (fun _ mn => ∃ sn, BveBceStepInv TmkInv c F0 F_cur s scr2 np nn R sn mn) ?_ ?_
        · rintro Jnxt _ mn ⟨sn, hstepn⟩; rw [Blocks.get_here]; bve_jump
          have hi1 : (i + 1#32).toNat = i.toNat + 1 := by
            rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
              Nat.mod_eq_of_lt (by omega : i.toNat + 1 < 2 ^ 32)]
          exact ihlp (i + 1#32, PUnit.unit) mn (by dsimp only; rw [hi1]; omega)
            ⟨sn, by rw [hi1]; omega, hstepn⟩
        · intro Jnxt hJnxt
          bve_ld (c0_load_full_scratch_buf (i := i.setWidth 64) hi_scr hml)
          bve_lets
          refine wp_call_of_spec _ _ (hTryBce _ _ _ X ?_)
          simp only [vals_nil, vals_cons, Arg.val_var, Arg.val_imm]
          refine ⟨c, F0, F_cur, sl, R, rfl, hinvl,
            (by change pl.toNat < 2 * sl.core.cur_vars; rw [hpl_nat, hcvl]; omega),
            (by simp only [hi_eq]; rw [hwi_eq]; exact hpk i.toNat hi_nat),
            (by rw [h64_32]; omega),
            (fun j hj => by rw [h64_32, hbuf_l (64 + j) (by omega)]; exact hnj j hj),
            hml, ?_⟩
          rintro blk lm' tmp' m_tb stb hinv_tb hm_tb
          have htmk_tb : TmkInv stb := hTmk_cong htmkl rfl rfl
          have htb_p := (full_bve_tryBce_pres (s := sl) (s' := stb) rfl rfl hpk hnj).1
          have htb_n := (full_bve_tryBce_pres (s := sl) (s' := stb) rfl rfl hpk hnj).2
          have htb_scr_idx : (i.setWidth 64).toNat < stb.scratch.scratch_buf.length := hi_scr
          bve_jnz hblk
          · refine wp_join_group (ts := [])
              (fun _ mn => ∃ sn, BveBceStepInv TmkInv c F0 F_cur s scr2 np nn R sn mn) ?_ ?_
            · rintro J_try _ mn hmn; rw [Blocks.get_here]; bve_jump; exact hJnxt () mn hmn
            · intro J_try hJ_try
              bve_ld (c0_load_full_scratch_buf (i := i.setWidth 64) htb_scr_idx hm_tb)
              bve_jnz hbin_flag
              · refine wp_join_group (ts := [])
                  (fun _ mn => ∃ sn, BveBceStepInv TmkInv c F0 F_cur s scr2 np nn R sn mn) ?_ ?_
                · rintro Jb _ mn hmn; rw [Blocks.get_here]; bve_jump; exact hJ_try () mn hmn
                · intro Jb hJb
                  bve_ld (c0_load_full_scratch_buf (i := i.setWidth 64) htb_scr_idx hm_tb)
                  bve_lets
                  refine wp_call_of_spec _ _ (hExtPush2 _ _ _ _ _ X ?_)
                  simp only [Arg.val_var]
                  refine ⟨c, stb, R, ⟨rfl, hinv_tb.2.2.2.2.1.2⟩, hinv_tb.1, htmk_tb, hm_tb, ?_⟩
                  rintro ⟨okp, ⟨⟩⟩ se2 m_e2 hcore_e2 hlen_e2
                    ⟨hll_e2, hext_e2, hscr_e2⟩ htmk_e2 hm_e2
                  have hstep_e2 := bve_bce_ext_post hinv_tb hcvl hfll hbuf_l htb_p htb_n
                    hcore_e2 hlen_e2 hll_e2 hext_e2 hscr_e2 htmk_e2 hm_e2
                  have ⟨hinv_e2, _, hcv_e2, hfl_e2, hbuf_e2, he2_p, he2_n, _⟩ := hstep_e2
                  bve_jnz hokp
                  · bve_ld (c0_load_full_scratch_buf (i := i.setWidth 64)
                        (by rw [hinv_e2.1.scratch_ok.scratch_buf_len]; omega) hm_e2)
                    bve_lets
                    refine wp_call_of_spec _ _ (hDelBin _ _ _ X ?_)
                    simp only [vals_nil, vals_cons, Arg.val_var]
                    refine ⟨c, se2, R, rfl, hinv_e2.1, hinv_e2.2.1.watches.layout, hm_e2, ?_⟩
                    rintro wvec' wstk' wu' nb' m_db sdb hlen_db _ hwat_fn hm_db
                    have hinv_db := FullBveVarHelpers.FullDenseInvW.of_deleteBinary
                      hinv_e2 hlen_db (hwat_fn F_cur hinv_e2.2.1.watches)
                    have hdb_ok := full_bve_tryBce_pres (s := se2) (s' := sdb) rfl rfl he2_p he2_n
                    bve_ld load_full_bce_cnt hm_db
                    bve_st m_bce1, hm_bce1 := store_full_bce_cnt
                      (sdb.scratch.bce_cnt + 1#64) hm_db
                    bve_jump
                    let sbce : FullState := { sdb with scratch :=
                      { sdb.scratch with bce_cnt := sdb.scratch.bce_cnt + 1#64 } }
                    have hbc_ok := full_bve_tryBce_pres (s := sdb) (s' := sbce)
                      rfl rfl hdb_ok.1 hdb_ok.2
                    exact hJb () m_bce1 ⟨sbce,
                      FullBveVarHelpers.FullDenseInvW.with_bce_cnt hinv_db _,
                      hTmk_cong htmk_e2 rfl rfl, hcv_e2, hfl_e2, hbuf_e2,
                      hbc_ok.1, hbc_ok.2, hm_bce1⟩
                  · bve_jump; exact hJb () m_e2 ⟨se2, hstep_e2⟩
              · refine wp_join_group (ts := [])
                  (fun _ mn => ∃ sn, BveBceStepInv TmkInv c F0 F_cur s scr2 np nn R sn mn) ?_ ?_
                · rintro Jl _ mn hmn; rw [Blocks.get_here]; bve_jump; exact hJ_try () mn hmn
                · intro Jl hJl
                  bve_ld (c0_load_full_scratch_buf (i := i.setWidth 64) htb_scr_idx hm_tb)
                  bve_lets
                  refine wp_call_of_spec _ _ (hExtPushCl _ _ _ _ _ X ?_)
                  simp only [Arg.val_var]
                  refine ⟨c, stb, R, ⟨rfl, hinv_tb.2.2.2.2.1.2⟩, hinv_tb.1, htmk_tb, hm_tb, ?_⟩
                  rintro ⟨okp, ⟨⟩⟩ se2 m_e2 hcore_e2 hlen_e2
                    ⟨hll_e2, hext_e2, hscr_e2⟩ htmk_e2 hm_e2
                  have hstep_e2 := bve_bce_ext_post hinv_tb hcvl hfll hbuf_l htb_p htb_n
                    hcore_e2 hlen_e2 hll_e2 hext_e2 hscr_e2 htmk_e2 hm_e2
                  have ⟨hinv_e2, _, hcv_e2, hfl_e2, hbuf_e2, he2_p, he2_n, _⟩ := hstep_e2
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
                      have h0 : se2.scratch.scratch_buf[i.toNat]? = some ccr := by
                        rw [← hi_eq, List.getElem?_eq_getElem (by rw [hscr_e2_len]; omega)]
                      rw [← h0.symm.trans (hbuf_e2 i.toNat (by omega))]; rfl
                    have hnb_ccr : (ccr &&& 0x80000000#32) = 0#32 := by
                      have h0 : (stb.scratch.scratch_buf[(i.setWidth 64).toNat]'htb_scr_idx &&&
                          0x80000000#32) = 0#32 := bne_eq_false_iff_eq.mp hbin_flag
                      simpa only [ccr, hscr_e2] using h0
                    have hbce_ccr := he2_p i.toNat hi_nat
                    rw [← hccr_eq] at hbce_ccr
                    unfold FullBveVarSpecs.FullBveTryBceEntryOk at hbce_ccr
                    simp only [hnb_ccr, ne_eq, not_true_eq_false, ↓reduceIte] at hbce_ccr
                    have hccr_nat : (ccr.setWidth 64).toNat = ccr.toNat := by
                      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt
                        (by have := ccr.isLt; omega : ccr.toNat < 2 ^ 64)]
                    have hccr_ar : (ccr.setWidth 64).toNat < se2.core.arena.length := by
                      rw [hccr_nat]; omega
                    have hccr_sz : 3 ≤ fullArenaClauseSize se2 ccr.toNat :=
                      (hinv_e2.2.1.arena.refs_wf ccr.toNat hbce_ccr.1).2.1
                    have hccr_p2 : ((ccr.setWidth 64) + 2#64).toNat < se2.core.arena.length := by
                      rw [BitVec.toNat_add, show (2#64 : BitVec 64).toNat = 2 from rfl, hccr_nat,
                        Nat.mod_eq_of_lt (by omega : ccr.toNat + 2 < 2 ^ 64)]
                      unfold fullArenaClauseSize fullArenaClauseSizeCore at hbce_ccr; omega
                    have har_eq :
                        se2.core.arena.set (ccr.setWidth 64).toNat
                          (se2.core.arena[(ccr.setWidth 64).toNat]'hccr_ar ||| 0x00080000#32) =
                        se2.core.arena.set ccr.toNat
                          (fullArenaHdr se2 ccr.toNat ||| 0x00080000#32) := by
                      unfold fullArenaHdr fullArenaHdrCore
                      rw [← hccr_nat, List.getElem?_eq_getElem hccr_ar, Option.getD_some]
                    bve_ld (c0_load_full_arena (i := ccr.setWidth 64) hccr_ar hm_e2)
                    bve_st m_ar, hm_ar := c0_store_full_arena (i := ccr.setWidth 64)
                      (se2.core.arena[(ccr.setWidth 64).toNat]'hccr_ar ||| 0x00080000#32)
                      hccr_ar hm_e2
                    bve_ld load_full_arena_garbage hm_ar
                    bve_ld (c0_load_full_arena (i := ccr.setWidth 64 + 2#64)
                      (by rw [List.length_set]; exact hccr_p2) hm_ar)
                    bve_st m_ag, hm_ag := store_full_arena_garbage _ hm_ar
                    bve_ld load_full_bce_cnt hm_ag
                    bve_st m_bce1, hm_bce1 := store_full_bce_cnt _ hm_ag
                    bve_jump
                    simp only [har_eq] at hm_bce1
                    exact hJl () m_bce1 (bve_bce_markGarb_post hTmk_cong (fun _ => trivial)
                      hinv_e2 htmk_e2 hcv_e2 hfl_e2 hbuf_e2 he2_p he2_n hbce_ccr.1 _ hm_bce1)
                  · bve_jump; exact hJl () m_e2 ⟨se2, hstep_e2⟩
          · bve_jump
            exact hJnxt () m_tb ⟨stb, hinv_tb, htmk_tb, hcvl, hfll, hbuf_l, htb_p, htb_n, hm_tb⟩
      · bve_ret
        exact hQ 1#64 sl ml hinvl.toDense htmkl (by rw [← hcvl]; exact Nat.le_refl _)
          hfll (Or.inl rfl) (fun h => by cases h) hml)

private def m5BvePureElimExpr (h : Val i64) (v pl nl np nn : Val i32) (ext_ok : Val .bool)
    (J : Cont []) : Expr Val Cont [i64] :=
  Expr.jnz (Arg.var ext_ok)
    (Expr.group (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
       Expr.group (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
         Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                     args := (Arg.var h, Arg.imm 760, ()) } fun po =>
         Expr.store (Arg.imm (t := i64) 1#64) (Arg.var po.1) (Expr.ret (Arg.imm 2, ())))
         Blocks.nil)
       fun Joom =>
       Expr.group (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
         Expr.group (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
           Expr.call "full_set_inactive" (as := [i64, i32, i32]) (bs := [])
             (Arg.var h, Arg.var v, Arg.imm 2, ()) fun _ =>
           Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                       args := (Arg.var h, Arg.imm 1088, ()) } fun p1 =>
           Expr.load i64 (Arg.var p1.1) fun ld =>
           Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                       args := (Arg.var ld, Arg.imm 1, ()) } fun p2 =>
           Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                       args := (Arg.var h, Arg.imm 1088, ()) } fun p3 =>
           Expr.store (Arg.var p2.1) (Arg.var p3.1) (Expr.ret (Arg.imm 1, ()))) Blocks.nil)
         fun Jinact =>
         Expr.let_ { sig := [i32, i32], code := OpCode.cmp .ugt i32,
                     args := (Arg.var nn, Arg.imm 0, ()) } fun c =>
         Expr.jnz (Arg.var c.1)
           (Expr.call "full_bve_weaken" (as := [i64, i32, i32, i32]) (bs := [.bool])
              (Arg.var h, Arg.var nl, Arg.imm 64, Arg.var nn, ()) fun ok2 =>
            Expr.jnz (Arg.var ok2.1) (Expr.jump Jinact.1 ()) (Expr.jump Joom.1 ()))
           (Expr.jump Jinact.1 ())) Blocks.nil)
       fun Jnn =>
       Expr.let_ { sig := [i32, i32], code := OpCode.cmp .ugt i32,
                   args := (Arg.var np, Arg.imm 0, ()) } fun c =>
       Expr.jnz (Arg.var c.1)
         (Expr.call "full_bve_weaken" (as := [i64, i32, i32, i32]) (bs := [.bool])
           (Arg.var h, Arg.var pl, Arg.imm 0, Arg.var np, ()) fun ok1 =>
          Expr.jnz (Arg.var ok1.1) (Expr.jump Jnn.1 ()) (Expr.jump Joom.1 ()))
         (Expr.jump Jnn.1 ())) Blocks.nil)
     fun J1 =>
     Expr.let_ { sig := [i32, i32], code := OpCode.cmp .eq i32,
                 args := (Arg.var np, Arg.imm 0, ()) } fun c0 =>
     Expr.jnz (Arg.var c0.1) (Expr.jump J1.1 ())
       (Expr.let_ { sig := [i32, i32], code := OpCode.cmp .eq i32,
                    args := (Arg.var nn, Arg.imm 0, ()) } fun c1 =>
        Expr.jnz (Arg.var c1.1) (Expr.jump J1.1 ()) (Expr.jump J ())))
    (Expr.jump J ())

private theorem m5_bve_pure_elim_wp (Γ : Env) (TmkInv : FullState → Prop)
    (hTmk_cong : ∀ {s s' : FullState}, TmkInv s → s'.core.cur_vars = s.core.cur_vars →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark → TmkInv s')
    (hWeaken : ∀ (h : BitVec 64) (blk_lit off cnt : BitVec 32) m Q X,
      (∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
        h = c.hdr ∧ FullBveVarSpecs.FullDenseInvW c F0 F_cur s ∧ TmkInv s ∧
        blk_lit.toNat < 2 * s.core.cur_vars ∧ off.toNat + cnt.toNat ≤ c.scratch_cap ∧
        (∀ i < cnt.toNat,
          FullBveVarSpecs.FullBveWeakItemOk s (s.scratch.scratch_buf[off.toNat + i]?.getD 0#32)) ∧
        (FullMem c s ⋆ R) m ∧
        ∀ (ok : Bool) s' m',
          FullBveVarSpecs.FullDenseInvW c F0 F_cur s' → TmkInv s' →
          s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
          s'.scratch.scratch_buf = s.scratch.scratch_buf →
          fullArenaClauseRefs s' = fullArenaClauseRefs s →
          (FullMem c s' ⋆ R) m' → Q (ok, ()) m') →
      Γ "full_bve_weaken" [i64, i32, i32, i32] [.bool] (h, blk_lit, off, cnt, ()) m Q X)
    (hSetInact : ∀ xs m Q X, FullBveVarSpecs.fullSetInactiveSpec xs m Q X →
      Γ "full_set_inactive" [i64, i32, i32] [] xs m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s s2 : FullState}
    {R : Mem 64 → Prop} {v pl nl np nn : BitVec 32} {ext_ok : Bool} {m2 : Mem 64}
    {Q : Post [i64]} {X : XPost} {J : Cont []}
    (hv_lt : v.toNat < s.core.cur_vars) (hpl_nat : pl.toNat = 2 * v.toNat)
    (hnl_nat : nl.toNat = 2 * v.toNat + 1)
    (hnp_le : np.toNat ≤ 64) (hnn_le : nn.toNat ≤ 64) (hsc512 : 512 ≤ c.scratch_cap)
    (hinv2 : FullBveVarSpecs.FullDenseInvW c F0 F_cur s2) (htmk2 : TmkInv s2)
    (hs2_cv : s2.core.cur_vars = s.core.cur_vars) (hs2_fl : s2.core.fuel = s.core.fuel)
    (hp_ok : ∀ i < np.toNat, FullBveVarSpecs.FullBveEntryOkW F_cur s2 (2 * v.toNat)
      (s2.scratch.scratch_buf[i]?.getD 0#32))
    (hn_ok : ∀ j < nn.toNat, FullBveVarSpecs.FullBveEntryOkW F_cur s2 (2 * v.toNat + 1)
      (s2.scratch.scratch_buf[64 + j]?.getD 0#32))
    (hm2 : (FullMem c s2 ⋆ R) m2) (hJ : J () m2)
    (hQ : ∀ r s' m',
      FullBveVarSpecs.FullDenseInv c F0 s' → TmkInv s' →
      s.core.cur_vars ≤ s'.core.cur_vars → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    wp Γ Q X (m5BvePureElimExpr c.hdr v pl nl np nn ext_ok J) m2 := by
  have h0_32 : (0 : BitVec 32).toNat = 0 := rfl
  have h64_32 : (64 : BitVec 32).toNat = 64 := rfl
  unfold m5BvePureElimExpr
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · refine wp_join_group (ts := []) (fun _ ml => (np = 0#32 ∨ nn = 0#32) ∧ ml = m2) ?_ ?_
    · rintro J1 _ ml ⟨_, h_ml⟩; subst ml; rw [Blocks.get_here]
      refine wp_join_group (ts := []) (fun _ ml =>
          ∃ sw, FullBveVarSpecs.FullDenseInvW c F0 F_cur sw ∧ TmkInv sw ∧
            sw.core.cur_vars = s.core.cur_vars ∧ sw.core.fuel = s.core.fuel ∧
            (FullMem c sw ⋆ R) ml) ?_ ?_
      · rintro J_oom _ ml ⟨sw, hinvw, htmkw, hcvw, hflw, hmw⟩
        rw [Blocks.get_here]
        bve_st ml1, hm_oom := store_full_oom 1#64 hmw
        bve_ret
        let sw_o : FullState := { sw with core := { sw.core with oom := 1#64 } }
        exact hQ 2#64 sw_o ml1 (FullBveVarHelpers.FullDenseInvW.with_oom hinvw 1#64).toDense
          (hTmk_cong htmkw rfl rfl) (by rw [← hcvw]; exact Nat.le_refl _)
          (by rw [← hflw]; exact Nat.le_refl _) (Or.inr (Or.inl rfl)) (fun h => by cases h) hm_oom
      · intro J_oom hJ_oom
        refine wp_join_group (ts := []) (fun _ ml =>
            ∃ sw, FullBveVarSpecs.FullDenseInvW c F0 F_cur sw ∧ TmkInv sw ∧
              sw.core.cur_vars = s.core.cur_vars ∧ sw.core.fuel = s.core.fuel ∧
              fullArenaClauseRefs sw = fullArenaClauseRefs s2 ∧
              sw.scratch.scratch_buf = s2.scratch.scratch_buf ∧ (FullMem c sw ⋆ R) ml) ?_ ?_
        · rintro J_nn _ ml ⟨sw, hinvw, htmkw, hcvw, hflw, hrefs_sw, hscr_sw, hmw⟩
          rw [Blocks.get_here]
          refine wp_join_group (ts := []) (fun _ ml =>
              ∃ sw1, FullBveVarSpecs.FullDenseInvW c F0 F_cur sw1 ∧ TmkInv sw1 ∧
                sw1.core.cur_vars = s.core.cur_vars ∧ sw1.core.fuel = s.core.fuel ∧
                (FullMem c sw1 ⋆ R) ml) ?_ ?_
          · rintro J_inact _ ml1 ⟨sw1, hinvw1, htmkw1, hcvw1, hflw1, hmw1⟩
            rw [Blocks.get_here]
            refine wp_call_of_spec _ _ (hSetInact _ _ _ X ?_)
            simp only [vals_nil, vals_cons, Arg.val_var, Arg.val_imm]
            refine ⟨c, sw1, R, rfl, hinvw1.1, hmw1, ?_⟩
            intro flags' unass' m_si hfl_len hm_si
            let sw2 : FullState := { sw1 with core :=
              { sw1.core with flags := flags', unassigned := unass' } }
            have hinvw2 := FullBveVarHelpers.FullDenseInvW.with_flags_unassigned
              hinvw1 hfl_len unass'
            bve_ld load_full_bve_cnt hm_si
            bve_st ml_bve, hm_bve := store_full_bve_cnt (sw2.scratch.bve_cnt + 1#64) hm_si
            bve_ret
            let sw3 : FullState := { sw2 with scratch :=
              { sw2.scratch with bve_cnt := sw2.scratch.bve_cnt + 1#64 } }
            exact hQ 1#64 sw3 ml_bve
              (FullBveVarHelpers.FullDenseInvW.with_bve_cnt hinvw2
                (sw2.scratch.bve_cnt + 1#64)).toDense
              (hTmk_cong htmkw1 rfl rfl) (by rw [← hcvw1]; exact Nat.le_refl _)
              (by rw [← hflw1]; exact Nat.le_refl _) (Or.inl rfl) (fun h => by cases h) hm_bve
          · intro J_inact hJ_inact
            bve_jnz hnn_pos
            · refine wp_call_of_spec _ _ (hWeaken _ _ _ _ _ _ X ?_)
              simp only [Arg.val_var, Arg.val_imm]
              refine ⟨c, F0, F_cur, sw, R, rfl, hinvw, htmkw,
                (by rw [hnl_nat, hcvw]; omega),
                (by rw [h64_32]; omega),
                (fun j hj => by
                  rw [hscr_sw, h64_32]
                  exact fullBveWeakItemOk_of_pres (by rw [hcvw, hs2_cv]) hrefs_sw
                    (FullBveVarHelpers.FullBveEntryOkW.to_weak (hn_ok j hj))), hmw, ?_⟩
              intro ok2 sw' m_w2 hinvw' htmkw' hcvw' hflw' _ _ hm_w2
              bve_jnz hok2
              · bve_jump; exact hJ_inact () m_w2 ⟨sw', hinvw', htmkw',
                  hcvw'.trans hcvw, hflw'.trans hflw, hm_w2⟩
              · bve_jump; exact hJ_oom () m_w2 ⟨sw', hinvw', htmkw',
                  hcvw'.trans hcvw, hflw'.trans hflw, hm_w2⟩
            · bve_jump; exact hJ_inact () ml ⟨sw, hinvw, htmkw, hcvw, hflw, hmw⟩
        · intro J_nn hJ_nn
          bve_jnz hnp_pos
          · refine wp_call_of_spec _ _ (hWeaken _ _ _ _ _ _ X ?_)
            simp only [Arg.val_var, Arg.val_imm]
            refine ⟨c, F0, F_cur, s2, R, rfl, hinv2, htmk2,
              (by change pl.toNat < 2 * s2.core.cur_vars; rw [hpl_nat, hs2_cv]; omega),
              (by rw [h0_32]; omega),
              (fun i hi => by
                rw [h0_32, Nat.zero_add]
                exact FullBveVarHelpers.FullBveEntryOkW.to_weak (hp_ok i hi)), hm2, ?_⟩
            intro ok1 s2' m_w1 hinvw1 htmkw1 hcv1 hfl1 hscr_w1 hrefs_w1 hm_w1
            bve_jnz hok1
            · bve_jump; exact hJ_nn () m_w1 ⟨s2', hinvw1, htmkw1, hcv1.trans hs2_cv,
                hfl1.trans hs2_fl, hrefs_w1, hscr_w1, hm_w1⟩
            · bve_jump; exact hJ_oom () m_w1 ⟨s2', hinvw1, htmkw1, hcv1.trans hs2_cv,
                hfl1.trans hs2_fl, hm_w1⟩
          · bve_jump; exact hJ_nn () m2 ⟨s2, hinv2, htmk2, hs2_cv, hs2_fl, rfl, rfl, hm2⟩
    · intro J1 hJ1
      bve_jnz hnp0
      · bve_jump; exact hJ1 () m2 ⟨Or.inl (by simpa using hnp0), rfl⟩
      · bve_jnz hnn0
        · bve_jump; exact hJ1 () m2 ⟨Or.inr (by simpa using hnn0), rfl⟩
        · bve_jump; exact hJ
  · bve_jump; exact hJ

/-! ## 2. Parametric Core Proof `m5_bve_var_core_wp` -/

private theorem m5_bve_var_core_wp (Γ : Env) (TmkInv : FullState → Prop)
    (hTmk_cong : ∀ {s s' : FullState}, TmkInv s → s'.core.cur_vars = s.core.cur_vars →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark → TmkInv s')
    (hDefrag : ∀ xs m Q X, fullWstackDefragSpec xs m Q X →
      Γ "full_wstack_defrag" [i64] [] xs m Q X)
    (hCollect : ∀ xs m Q X, FullBveVarSpecs.fullBveCollectSpec xs m Q X →
      Γ "full_bve_collect" [i64, i32, i64, i32] [i32] xs m Q X)
    (hExtNeed : ∀ xs m Q X, FullBveVarSpecs.fullBveExtNeedSpec xs m Q X →
      Γ "full_bve_ext_need" [i64, i32, i32] [i64] xs m Q X)
    (hWeaken : ∀ (h : BitVec 64) (blk_lit off cnt : BitVec 32) m Q X,
      (∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
        h = c.hdr ∧ FullBveVarSpecs.FullDenseInvW c F0 F_cur s ∧ TmkInv s ∧
        blk_lit.toNat < 2 * s.core.cur_vars ∧ off.toNat + cnt.toNat ≤ c.scratch_cap ∧
        (∀ i < cnt.toNat,
          FullBveVarSpecs.FullBveWeakItemOk s (s.scratch.scratch_buf[off.toNat + i]?.getD 0#32)) ∧
        (FullMem c s ⋆ R) m ∧
        ∀ (ok : Bool) s' m',
          FullBveVarSpecs.FullDenseInvW c F0 F_cur s' → TmkInv s' →
          s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
          s'.scratch.scratch_buf = s.scratch.scratch_buf →
          fullArenaClauseRefs s' = fullArenaClauseRefs s →
          (FullMem c s' ⋆ R) m' → Q (ok, ()) m') →
      Γ "full_bve_weaken" [i64, i32, i32, i32] [.bool] (h, blk_lit, off, cnt, ()) m Q X)
    (hSetInact : ∀ xs m Q X, FullBveVarSpecs.fullSetInactiveSpec xs m Q X →
      Γ "full_set_inactive" [i64, i32, i32] [] xs m Q X)
    (hGates : ∀ (h : BitVec 64) (v np nn : BitVec 32) m Q X,
      (∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
        h = c.hdr ∧ FullBveVarSpecs.FullDenseInvW c F0 F_cur s ∧ 132 ≤ c.scratch_cap ∧ TmkInv s ∧
        v.toNat < s.core.cur_vars ∧ np.toNat ≤ 64 ∧ nn.toNat ≤ 64 ∧
        (∀ i < np.toNat, FullBveVarSpecs.FullBveEntryOkW F_cur s (2 * v.toNat)
          (s.scratch.scratch_buf[i]?.getD 0#32)) ∧
        (∀ j < nn.toNat, FullBveVarSpecs.FullBveEntryOkW F_cur s (2 * v.toNat + 1)
          (s.scratch.scratch_buf[64 + j]?.getD 0#32)) ∧
        (FullMem c s ⋆ R) m ∧
        ∀ s' m',
          FullBveVarSpecs.FullDenseInvW c F0 F_cur s' → TmkInv s' →
          s'.core.cur_vars = s.core.cur_vars →
          s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
          s'.core.fuel.toNat ≤ s.core.fuel.toNat →
          (∀ i < 128, s'.scratch.scratch_buf[i]? = s.scratch.scratch_buf[i]?) →
          (FullMem c s' ⋆ R) m' → Q () m') →
      Γ "full_bve_gates" [i64, i32, i32, i32] [] (h, v, np, nn, ()) m Q X)
    (hResolve : ∀ xs m Q X, FullBveVarSpecs.fullBveResolvePairSpec xs m Q X →
      Γ "full_bve_resolve_pair" [i64, i32, i32, i32] [.bool] xs m Q X)
    (hCommitRes : ∀ (h r_off r_end : BitVec 64) m Q X,
      (∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
        h = c.hdr ∧ FullBveVarSpecs.FullDenseInvW c F0 F_cur s ∧ TmkInv s ∧
        r_off.toNat ≤ r_end.toNat ∧ r_end.toNat ≤ c.scratch_cap ∧
        FullBveVarSpecs.FullResBufOkW F_cur s r_end.toNat r_off.toNat ∧ (FullMem c s ⋆ R) m ∧
        ∀ r s' m',
          FullBveVarSpecs.FullDenseInvW c F0 F_cur s' → TmkInv s' →
          s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
          (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
          (FullMem c s' ⋆ R) m' → Q (r, ()) m') →
      Γ "full_bve_commit_res" [i64, i64, i64] [i64] (h, r_off, r_end, ()) m Q X)
    (hTryBce : ∀ xs m Q X, FullBveVarSpecs.fullBveTryBceSpec xs m Q X →
      Γ "full_bve_try_bce" [i64, i32, i32, i32, i32] [.bool] xs m Q X)
    (hExtPush2 : ∀ (h : BitVec 64) (blk ot : BitVec 32) m Q X,
      (∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
        (h = c.hdr ∧ s.scratch.extend_len ≤ c.extend_cap) ∧ s.LengthsOk c ∧ TmkInv s ∧
        (FullMem c s ⋆ R) m ∧
        ∀ (r : Tup Val [.bool]) s' m',
          PreservesCoreSlice (fullSafetySlice c).coreProj s s' → s'.LengthsOk c →
          (s'.scratch.last_learned = s.scratch.last_learned ∧
           s'.scratch.extend_len ≤ c.extend_cap ∧
           s'.scratch.scratch_buf = s.scratch.scratch_buf) →
          TmkInv s' → (FullMem c s' ⋆ R) m' → Q r m') →
      Γ "full_extend_push2" [i64, i32, i32] [.bool] (h, blk, ot, ()) m Q X)
    (hDelBin : ∀ xs m Q X, FullBveVarSpecs.fullDeleteBinarySpec xs m Q X →
      Γ "full_delete_binary" [i64, i32, i32] [] xs m Q X)
    (hExtPushCl : ∀ (h : BitVec 64) (blk cr : BitVec 32) m Q X,
      (∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
        (h = c.hdr ∧ s.scratch.extend_len ≤ c.extend_cap) ∧ s.LengthsOk c ∧ TmkInv s ∧
        (FullMem c s ⋆ R) m ∧
        ∀ (r : Tup Val [.bool]) s' m',
          PreservesCoreSlice (fullSafetySlice c).coreProj s s' → s'.LengthsOk c →
          (s'.scratch.last_learned = s.scratch.last_learned ∧
           s'.scratch.extend_len ≤ c.extend_cap ∧
           s'.scratch.scratch_buf = s.scratch.scratch_buf) →
          TmkInv s' → (FullMem c s' ⋆ R) m' → Q r m') →
      Γ "full_extend_push_cl" [i64, i32, i32] [.bool] (h, blk, cr, ()) m Q X)
    {c : FullCfg} {F0 : CNF Nat} {s : FullState} {R : Mem 64 → Prop} {v : BitVec 32}
    {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hdense : FullBveVarSpecs.FullDenseInv c F0 s) (htmk0 : TmkInv s)
    (hv_lt : v.toNat < s.core.cur_vars) (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ r s' m',
      FullBveVarSpecs.FullDenseInv c F0 s' → TmkInv s' →
      s.core.cur_vars ≤ s'.core.cur_vars → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    Func.wp Γ full_bve_var_m5_body (c.hdr, v, ()) m Q X := by
  obtain ⟨F_cur, hinv⟩ := fullDenseInv_exists_witness hdense
  have hmv := c.hmaxv; have harc := c.harena; have hsc := c.hscr
  unfold dimacsBound at hmv harc hsc
  have hcv_le : s.core.cur_vars ≤ c.max_vars := hinv.1.core_ok.cur_vars_le
  have hv_lt32 : 2 * v.toNat < 2 ^ 32 := by omega
  let pl := v <<< ((1 : BitVec 32).toNat % 32)
  have hpl_nat : pl.toNat = 2 * v.toNat := by dsimp only [pl]; exact bv32_shl1_toNat hv_lt32
  have hnl_nat : (pl ||| 1#32).toNat = 2 * v.toNat + 1 := bv32_or1_even_toNat hpl_nat
  unfold Func.wp full_bve_var_m5_body
  bve_ld load_full_oom hm
  bve_jnz hoom0
  · bve_ret
    exact hQ 2#64 s m hdense htmk0 (Nat.le_refl _) (Nat.le_refl _) (Or.inr (Or.inl rfl))
      (fun h => by cases h) hm
  · bve_ld load_full_scratch_cap hm
    bve_jnz hsc_ult
    · bve_ret
      exact hQ 1#64 s m hdense htmk0 (Nat.le_refl _) (Nat.le_refl _) (Or.inl rfl)
        (fun h => by cases h) hm
    · have hsc512 : 512 ≤ c.scratch_cap := by
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
        (by rw [show (64 : BitVec 32).toNat = 64 from rfl]; omega), hm, ?_⟩
      dsimp only; rintro np scr1 m1 hlen1 hkeep1 hres1 hm1
      let s1 : FullState := { s with scratch := { s.scratch with scratch_buf := scr1 } }
      have hinv1 := FullBveVarHelpers.FullDenseInvW.with_scratch_buf hinv hlen1
      have htmk1 : TmkInv s1 := hTmk_cong htmk0 rfl rfl
      have hptr64 : c.pScratchBuf + (BitVec.signExtend 64 64#32) * 4 =
          c.pScratchBuf + BitVec.ofNat 64 (4 * 64) := by
        apply congrArg (c.pScratchBuf + ·); decide
      bve_lets
      refine wp_call_of_spec _ _ (hCollect _ _ _ X ?_)
      simp only [vals_nil, vals_cons, Arg.val_var, Arg.val_imm]
      refine ⟨c, F0, F_cur, s1, 64, R, rfl, hinv1,
        (by change (pl ||| 1#32).toNat < 2 * s.core.cur_vars; rw [hnl_nat]; omega),
        hptr64, (by rw [show (64 : BitVec 32).toNat = 64 from rfl]; omega), hm1, ?_⟩
      dsimp only; rintro nn scr2 m2 hlen2 hkeep2 hres2 hm2
      let s2 : FullState := { s1 with scratch := { s1.scratch with scratch_buf := scr2 } }
      have hinv2 := FullBveVarHelpers.FullDenseInvW.with_scratch_buf hinv1 hlen2
      have htmk2 : TmkInv s2 := hTmk_cong htmk1 rfl rfl
      bve_jnz hnp_eq
      · bve_ret
        exact hQ 1#64 s2 m2 hinv2.toDense htmk2 (Nat.le_refl _) (Nat.le_refl _) (Or.inl rfl)
          (fun h => by cases h) hm2
      · bve_jnz hnn_eq
        · bve_ret
          exact hQ 1#64 s2 m2 hinv2.toDense htmk2 (Nat.le_refl _) (Nat.le_refl _) (Or.inl rfl)
            (fun h => by cases h) hm2
        · have hnp_ne : np ≠ 0xFFFFFFFF#32 := by intro h; rw [h] at hnp_eq; cases hnp_eq
          have hnn_ne : nn ≠ 0xFFFFFFFF#32 := by intro h; rw [h] at hnn_eq; cases hnn_eq
          have hnp_res : np.toNat ≤ 64 ∧
              ∀ i < np.toNat, FullBveVarSpecs.FullBveEntryOkW F_cur s1 pl.toNat
                (scr1[i]?.getD 0#32) := by
            rcases hres1 with rfl | h
            · exact absurd rfl hnp_ne
            · exact ⟨by simpa only [show (64 : BitVec 32).toNat = 64 from rfl] using h.1,
                fun i hi => by simpa only [Nat.zero_add] using h.2 i hi⟩
          have hnn_res : nn.toNat ≤ 64 ∧
              ∀ j < nn.toNat, FullBveVarSpecs.FullBveEntryOkW F_cur s2 (pl ||| 1#32).toNat
                (scr2[64 + j]?.getD 0#32) := by
            rcases hres2 with rfl | h
            · exact absurd rfl hnn_ne
            · exact ⟨by simpa only [show (64 : BitVec 32).toNat = 64 from rfl] using h.1, h.2⟩
          have hnp_le : np.toNat ≤ 64 := hnp_res.1
          have hnn_le : nn.toNat ≤ 64 := hnn_res.1
          have hp_ok : ∀ i < np.toNat,
              FullBveVarSpecs.FullBveEntryOkW F_cur s2 (2 * v.toNat) (scr2[i]?.getD 0#32) :=
            fun i hi => by
              rw [hkeep2 i (by omega) (Or.inl (by omega)), ← hpl_nat]
              exact FullBveVarHelpers.FullBveEntryOkW.with_state
                (Nat.le_refl _) rfl rfl (hnp_res.2 i hi)
          have hn_ok : ∀ j < nn.toNat,
              FullBveVarSpecs.FullBveEntryOkW F_cur s2 (2 * v.toNat + 1)
                (scr2[64 + j]?.getD 0#32) := fun j hj => by rw [← hnl_nat]; exact hnn_res.2 j hj
          have hs2_cv : s2.core.cur_vars = s.core.cur_vars := rfl
          have hs2_fl : s2.core.fuel = s.core.fuel := rfl
          have h0_32 : (0 : BitVec 32).toNat = 0 := rfl
          have h64_32 : (64 : BitVec 32).toNat = 64 := rfl
          bve_lets
          refine wp_call_of_spec _ _ (hExtNeed _ _ _ X ?_)
          simp only [vals_nil, vals_cons, Arg.val_var, Arg.val_imm]
          refine ⟨c, s2, R, rfl, hinv2.1, (by rw [h0_32]; omega),
            entries_to_extNeed hinv2 (off := 0) (lit := 2 * v.toNat) (fun i hi => by
              rw [Nat.zero_add]; exact hp_ok i hi), hm2, ?_⟩
          intro en1; bve_lets
          refine wp_call_of_spec _ _ (hExtNeed _ _ _ X ?_)
          simp only [vals_nil, vals_cons, Arg.val_var, Arg.val_imm]
          refine ⟨c, s2, R, rfl, hinv2.1, (by rw [h64_32]; omega),
            entries_to_extNeed hinv2 (off := 64) (lit := 2 * v.toNat + 1) hn_ok, hm2, ?_⟩
          intro en2
          bve_ld load_full_extend_len hm2
          bve_ld load_full_extend_cap hm2
          bve_lets
          refine wp_join_group (ts := []) (fun _ ml => ml = m2) ?_ ?_
          · rintro J _ ml h_ml; subst ml; rw [Blocks.get_here]
            bve_lets; bve_ld load_full_elim_bound hm2; bve_lets
            refine wp_join_group (ts := [i64, i64, .bool]) (fun (_rc_f, rp_f, fit_f, _) ml =>
                ∃ sf, FullBveVarSpecs.FullDenseInvW c F0 F_cur sf ∧ TmkInv sf ∧
                  sf.core.cur_vars = s2.core.cur_vars ∧ sf.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                  sf.core.arena = s2.core.arena ∧ sf.core.arena_len = s2.core.arena_len ∧
                  (∀ idx < 128, sf.scratch.scratch_buf[idx]? = scr2[idx]?) ∧
                  (fit_f = true → 160 ≤ rp_f.toNat ∧ rp_f.toNat ≤ c.scratch_cap ∧
                    FullBveVarSpecs.FullResBufOkW F_cur sf rp_f.toNat 160) ∧
                  (FullMem c sf ⋆ R) ml) ?_ ?_
            · rintro J_fit ⟨rc_f, rp_f, fit_f, ⟨⟩⟩ ml
                ⟨sf, hinvf, htmkf, hcvf, hflf, harf, half, hbuf_f, hres_f, hmf⟩
              rw [Blocks.get_here]; bve_lets
              refine wp_join_group (ts := []) (fun _ m_bce =>
                  ∃ sb, FullBveVarSpecs.FullDenseInvW c F0 F_cur sb ∧ TmkInv sb ∧
                    sb.core.cur_vars = s2.core.cur_vars ∧ sb.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                    sb.core.arena = s2.core.arena ∧ sb.core.arena_len = s2.core.arena_len ∧
                    (∀ idx < 128, sb.scratch.scratch_buf[idx]? = scr2[idx]?) ∧
                    (FullMem c sb ⋆ R) m_bce) ?_ ?_
              · rintro J_bce _ m_bce ⟨sb, hinvb, htmkb, hcvb, hflb, harb, halb, hbuf_b, hmb⟩
                rw [Blocks.get_here]
                have hpbce : ∀ i < np.toNat,
                    FullBveVarSpecs.FullBveTryBceEntryOk c sb (scr2[i]?.getD 0#32) := fun i hi =>
                  FullBveTryBceEntryOk.with_same_arena harb halb
                    (FullBveVarHelpers.FullBveEntryOkW.to_tryBceEntry hinv2 (hp_ok i hi))
                have hnbce : ∀ j < nn.toNat,
                    FullBveVarSpecs.FullBveTryBceOppOk c sb (scr2[64 + j]?.getD 0#32) := fun j hj =>
                  FullBveTryBceOppOk.with_same_arena harb halb
                    (FullBveVarHelpers.FullBveEntryOkW.to_tryBceOpp hinv2 (hn_ok j hj))
                have hbce := m5_bve_bce_loop_wp (X := X) Γ TmkInv hTmk_cong hTryBce hExtPush2
                  hDelBin hExtPushCl hv_lt hpl_nat hnp_le hnn_le hsc512 hinvb htmkb
                  (by rw [hcvb, hs2_cv]) hflb hbuf_b hpbce hnbce hmb hQ
                dsimp only [m5BveBceLoopExpr, bSteps, bStep, bLd64, bLet32, bCall32, bElse, bGrp0,
                  bGrpFit, bDummyTup, bDummyVal, i64, i32, full_bve_var_m5_body] at hbce
                exact hbce
              · intro J_bce hJ_bce
                bve_jnz hfit_c
                · bve_ld load_full_arena_len hmf
                  bve_ld load_full_arena_cap hmf
                  bve_jnz har_fit
                  · -- Read-only watch headroom pre-check + optional defrag before weaken
                    obtain ⟨hrp160, hrp_cap, hres_fit⟩ := hres_f hfit_c
                    have hscr_f := hinvf.1.scratch_ok.scratch_buf_len
                    have hwv_f := hinvf.1.core_ok.wvec_len
                    bve_ld load_full_watch_vec_ptr hmf
                    refine wp_loop_inv (ts := [i64, i64, i64])
                      (fun (_wa, _msz, wp_p, ()) mwp =>
                        mwp = ml ∧ wp_p.toNat ≤ rp_f.toNat ∧
                        FullBveVarSpecs.FullResBufOkW F_cur sf rp_f.toNat wp_p.toNat)
                      (fun (_, _, wp_p, _) _ => rp_f.toNat - wp_p.toNat)
                      (fun Jwp hJwp => by
                        bve_jump
                        exact hJwp (0#64, 0#64, 160#64, ()) ml ⟨rfl,
                          by rw [show (160#64 : BitVec 64).toNat = 160 from rfl]; exact hrp160,
                          by rw [show (160#64 : BitVec 64).toNat = 160 from rfl]; exact hres_fit⟩)
                      (fun Jwp ⟨wa, msz, wp_p, ⟨⟩⟩ mwp ⟨hmwp, hwp_le, hres_wp⟩ ihwp => ?_)
                    rcases hmwp.symm with rfl
                    rw [Blocks.get_here]; bve_jnz hwp_lt
                    · -- Body of `while (wp_p < rp)`
                      have hwp_nat : wp_p.toNat < rp_f.toNat := by
                        rw [BitVec.ult, decide_eq_true_eq] at hwp_lt; exact hwp_lt
                      have hwp_scr : wp_p.toNat < sf.scratch.scratch_buf.length := by omega
                      obtain ⟨hbd_wp, hlts_wp, htail_wp⟩ := bve_resBuf_head hres_wp hwp_nat
                      let rsz := sf.scratch.scratch_buf[wp_p.toNat]'hwp_scr
                      have hrsz_getD :
                          (sf.scratch.scratch_buf[wp_p.toNat]?.getD 0#32).toNat = rsz.toNat := by
                        dsimp only [rsz]; rw [List.getElem?_eq_getElem hwp_scr, Option.getD_some]
                      rw [hrsz_getD] at hbd_wp hlts_wp htail_wp
                      have hwp1_nat : (wp_p + 1#64).toNat = wp_p.toNat + 1 := by
                        rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl,
                          Nat.mod_eq_of_lt (by omega : wp_p.toNat + 1 < 2 ^ 64)]
                      have hwp_next_nat :
                          (wp_p + 1#64 + rsz.setWidth 64).toNat = wp_p.toNat + 1 + rsz.toNat := by
                        rw [BitVec.toNat_add, hwp1_nat, BitVec.toNat_setWidth,
                          Nat.mod_eq_of_lt (by omega : rsz.toNat < 2 ^ 64),
                          Nat.mod_eq_of_lt (by omega : wp_p.toNat + 1 + rsz.toNat < 2 ^ 64)]
                      bve_ld (c0_load_full_scratch_buf (i := wp_p) hwp_scr hmf)
                      refine wp_join_group (ts := [i64, i64])
                        (fun (_wa', _msz', ()) mg => mg = ml)
                        (fun _ ⟨wa', msz', ⟨⟩⟩ mg hmg => by
                          rcases hmg.symm with rfl; rw [Blocks.get_here]; bve_jump
                          exact ihwp (wa', msz', wp_p + 1#64 + rsz.setWidth 64, ()) ml
                            (by dsimp only; rw [hwp_next_nat]; omega)
                            ⟨rfl, by rw [hwp_next_nat]; exact hbd_wp,
                              by rw [hwp_next_nat]; exact htail_wp⟩)
                        (fun Jrsz hJrsz => ?_)
                      bve_jnz hrsz_ge2
                      · refine wp_join_group (ts := [i64]) (fun (_per, ()) mp => mp = ml)
                          (fun _ ⟨per, ⟨⟩⟩ mp hmp => ?_)
                          (fun Jper hJper => by
                            bve_jnz hper2
                            · bve_jump; exact hJper (1#64, ()) ml rfl
                            · bve_jump; exact hJper (2#64, ()) ml rfl)
                        rcases hmp.symm with rfl; rw [Blocks.get_here]
                        refine wp_loop_inv (ts := [i64, i64, i32])
                          (fun (_wa2, _msz2, wk, ()) mwk => mwk = ml ∧ wk.toNat ≤ rsz.toNat)
                          (fun (_, _, wk, _) _ => rsz.toNat - wk.toNat)
                          (fun Jwk hJwk => by
                            bve_jump; exact hJwk (wa, msz, 0#32, ()) ml ⟨rfl, Nat.zero_le _⟩)
                          (fun Jwk ⟨wa2, msz2, wk, ⟨⟩⟩ mwk ⟨hmwk, hwk_le⟩ ihwk => ?_)
                        rcases hmwk.symm with rfl; rw [Blocks.get_here]; bve_jnz hwk_lt
                        · have hwk_nat : wk.toNat < rsz.toNat := by
                            rw [BitVec.ult, decide_eq_true_eq] at hwk_lt; exact hwk_lt
                          have hwk1 : (wk + 1#32).toNat = wk.toNat + 1 := by
                            rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
                              Nat.mod_eq_of_lt (by omega : wk.toNat + 1 < 2 ^ 32)]
                          have hwk_idx_nat :
                              (wp_p + 1#64 + wk.setWidth 64).toNat = wp_p.toNat + 1 + wk.toNat := by
                            rw [BitVec.toNat_add, hwp1_nat, BitVec.toNat_setWidth,
                              Nat.mod_eq_of_lt (by omega : wk.toNat < 2 ^ 64),
                              Nat.mod_eq_of_lt (by omega : wp_p.toNat + 1 + wk.toNat < 2 ^ 64)]
                          have hwk_scr : (wp_p + 1#64 + wk.setWidth 64).toNat <
                              sf.scratch.scratch_buf.length := by rw [hwk_idx_nat]; omega
                          let wl := sf.scratch.scratch_buf[(wp_p + 1#64 + wk.setWidth 64).toNat]'
                            hwk_scr
                          have hwl_lt : wl.toNat < 2 * sf.core.cur_vars := by
                            have h1 := hlts_wp wk.toNat hwk_nat
                            have h2 : sf.scratch.scratch_buf[wp_p.toNat + 1 + wk.toNat]? =
                                some wl := by
                              dsimp only [wl]
                              rw [← hwk_idx_nat, List.getElem?_eq_getElem hwk_scr]
                            rw [h2, Option.getD_some] at h1; exact h1
                          have hwl_wv :
                              ((wl.setWidth 64 <<< ((1 : BitVec 64).toNat % 64)) + 1#64).toNat <
                                sf.core.wvec.length := by
                            rw [BitVec.toNat_add, BitVec.toNat_shiftLeft,
                              show ((1 : BitVec 64).toNat % 64) = 1 from rfl,
                              BitVec.toNat_setWidth,
                              Nat.mod_eq_of_lt (by omega : wl.toNat < 2 ^ 64),
                              Nat.shiftLeft_eq, Nat.mul_comm,
                              Nat.mod_eq_of_lt (by omega : 2 * wl.toNat < 2 ^ 64),
                              show (1#64 : BitVec 64).toNat = 1 from rfl,
                              Nat.mod_eq_of_lt (by omega : 2 * wl.toNat + 1 < 2 ^ 64), hwv_f]
                            omega
                          bve_ld (c0_load_full_scratch_buf (i := wp_p + 1#64 + wk.setWidth 64)
                            hwk_scr hmf)
                          bve_ld (c0_load_full_wvec
                            (i := (wl.setWidth 64 <<< ((1 : BitVec 64).toNat % 64)) + 1#64)
                            hwl_wv hmf)
                          refine wp_join_group (ts := [i64]) (fun (_msz3, ()) mm3 => mm3 = ml)
                            (fun _ ⟨msz3, ⟨⟩⟩ mm3 hmm3 => by
                              rcases hmm3.symm with rfl; rw [Blocks.get_here]; bve_jump
                              exact ihwk (wa2 + per, msz3, wk + 1#32, ()) ml
                                (by dsimp only; rw [hwk1]; omega) ⟨rfl, by rw [hwk1]; omega⟩)
                            (fun Jmx hJmx => by
                              bve_jnz hlsz_gt
                              · bve_jump; exact hJmx (_, ()) ml rfl
                              · bve_jump; exact hJmx (msz2, ()) ml rfl)
                        · bve_jump; exact hJrsz (wa2, msz2, ()) ml rfl
                      · bve_jump; exact hJrsz (wa, msz, ()) ml rfl
                    · -- Exit `wp_p < rp` -> optional `full_wstack_defrag`, then headroom check
                      bve_lets
                      refine wp_join_group (ts := [])
                        (fun _ md => ∃ sd,
                          FullBveVarSpecs.FullDenseInvW c F0 F_cur sd ∧ TmkInv sd ∧
                          sd.core.cur_vars = s2.core.cur_vars ∧
                          sd.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                          sd.core.arena = s2.core.arena ∧ sd.core.arena_len = s2.core.arena_len ∧
                          sd.scratch.scratch_buf = sf.scratch.scratch_buf ∧
                          (FullMem c sd ⋆ R) md)
                        (fun _ () md ⟨sd, hinvd, htmkd, hcvd, hfld, hard, hald, hscrd, hmd⟩ => ?_)
                        (fun Jdef hJdef => ?_)
                      · -- `if (h->wcap >= h->wlen && h->wcap - h->wlen >= w_need)`
                        rw [Blocks.get_here]
                        bve_ld load_full_wcap hmd
                        bve_ld load_full_wlen hmd
                        bve_jnz hw_ok1
                        · bve_ld load_full_wcap hmd
                          bve_ld load_full_wlen hmd
                          bve_jnz hw_ok2
                          · refine wp_join_group (ts := []) (fun _ m_o =>
                                ∃ so, FullBveVarSpecs.FullDenseInvW c F0 F_cur so ∧ TmkInv so ∧
                                  so.core.cur_vars = s.core.cur_vars ∧
                                  so.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                                  (FullMem c so ⋆ R) m_o) ?_ ?_
                            · rintro J_oom2 _ m_o ⟨so, hinvo, htmko, hcvo, hflo, hmo⟩
                              rw [Blocks.get_here]
                              bve_st m_o1, hm_o1 := store_full_oom 1#64 hmo
                              bve_ret
                              let so1 : FullState :=
                                { so with core := { so.core with oom := 1#64 } }
                              exact hQ 2#64 so1 m_o1
                                (FullBveVarHelpers.FullDenseInvW.with_oom hinvo 1#64).toDense
                                (hTmk_cong htmko rfl rfl) (by rw [← hcvo]; exact Nat.le_refl _) hflo
                                (Or.inr (Or.inl rfl)) (fun h => by cases h) hm_o1
                            · intro J_oom2 hJ_oom2
                              refine wp_call_of_spec _ _ (hWeaken _ _ _ _ _ _ X ?_)
                              simp only [Arg.val_var, Arg.val_imm]
                              refine ⟨c, F0, F_cur, sd, R, rfl, hinvd, htmkd,
                                (by change pl.toNat < 2 * sd.core.cur_vars
                                    rw [hpl_nat, hcvd, hs2_cv]; omega),
                                (by rw [h0_32]; omega),
                                (fun i hi => by
                                  rw [h0_32, Nat.zero_add, hscrd, hbuf_f i (by omega)]
                                  exact fullBveWeakItemOk_of_pres (by rw [hcvd, hs2_cv])
                                    (by unfold fullArenaClauseRefs fullArenaClauseRefsCore
                                        rw [hard, hald])
                                    (FullBveVarHelpers.FullBveEntryOkW.to_weak (hp_ok i hi))),
                                hmd, ?_⟩
                              intro ok1 sf1 m_w1 hinvf1 htmk1' hcv1 hfl1 hscr1 hrefs1 hm_w1
                              bve_jnz hok1
                              · refine wp_call_of_spec _ _ (hWeaken _ _ _ _ _ _ X ?_)
                                simp only [Arg.val_var, Arg.val_imm]
                                refine ⟨c, F0, F_cur, sf1, R, rfl, hinvf1, htmk1',
                                  (by change (pl ||| 1#32).toNat < 2 * sf1.core.cur_vars
                                      rw [hnl_nat, hcv1, hcvd, hs2_cv]; omega),
                                  (by rw [h64_32]; omega),
                                  (fun j hj => by
                                    rw [h64_32, hscr1, hscrd, hbuf_f (64 + j) (by omega)]
                                    exact fullBveWeakItemOk_of_pres (by rw [hcv1, hcvd, hs2_cv])
                                      (hrefs1.trans (by
                                        unfold fullArenaClauseRefs fullArenaClauseRefsCore
                                        rw [hard, hald]))
                                      (FullBveVarHelpers.FullBveEntryOkW.to_weak (hn_ok j hj))),
                                  hm_w1, ?_⟩
                                intro ok2 sf2 m_w2 hinvf2 htmk2' hcv2 hfl2 hscr2 _hrefs2 hm_w2
                                bve_jnz hok2
                                · refine wp_call_of_spec _ _ (hSetInact _ _ _ X ?_)
                                  simp only [vals_nil, vals_cons, Arg.val_var, Arg.val_imm]
                                  refine ⟨c, sf2, R, rfl, hinvf2.1, hm_w2, ?_⟩
                                  intro flags' unass' m_si hfl_len hm_si
                                  let sf3 : FullState := { sf2 with core :=
                                    { sf2.core with flags := flags', unassigned := unass' } }
                                  have hinvf3 :=
                                    FullBveVarHelpers.FullDenseInvW.with_flags_unassigned
                                    hinvf2 hfl_len unass'
                                  bve_ld load_full_bve_cnt hm_si
                                  bve_st m_bve, hm_bve := store_full_bve_cnt
                                    (sf3.scratch.bve_cnt + 1#64) hm_si
                                  bve_lets
                                  let sf4 : FullState := { sf3 with scratch :=
                                    { sf3.scratch with bve_cnt := sf3.scratch.bve_cnt + 1#64 } }
                                  have hinvf4 := FullBveVarHelpers.FullDenseInvW.with_bve_cnt hinvf3
                                    (sf3.scratch.bve_cnt + 1#64)
                                  have hres4 :
                                      FullBveVarSpecs.FullResBufOkW F_cur sf4 rp_f.toNat 160 :=
                                    FullBveVarHelpers.FullResBufOkW.with_state
                                      (by dsimp only [sf4, sf3]
                                          rw [hcv2, hcv1, hcvd, hcvf])
                                      (fun _ _ => by
                                        dsimp only [sf4, sf3]; rw [hscr2, hscr1, hscrd])
                                      hres_fit
                                  refine wp_call_of_spec _ _ (hCommitRes _ _ _ _ _ X ?_)
                                  simp only [Arg.val_var, Arg.val_imm]
                                  refine ⟨c, F0, F_cur, sf4, R, rfl, hinvf4,
                                    hTmk_cong htmk2' rfl rfl,
                                    (by rw [show (160 : BitVec 64).toNat = 160 from rfl]
                                        exact hrp160),
                                    hrp_cap,
                                    (by rw [show (160 : BitVec 64).toNat = 160 from rfl]
                                        exact hres4),
                                    hm_bve, ?_⟩
                                  intro r_cr sf_end m_end hinv_cr htmk_cr hcv_cr hfl_cr
                                    hrc_cr h20_cr
                                    hm_end
                                  exact hQ r_cr sf_end m_end hinv_cr.toDense htmk_cr
                                    (by rw [hcv_cr]; dsimp only [sf4, sf3]
                                        rw [hcv2, hcv1, hcvd, hs2_cv]; exact Nat.le_refl _)
                                    (by rw [hfl_cr]; dsimp only [sf4, sf3]; rw [hfl2, hfl1]
                                        exact hfld)
                                    hrc_cr h20_cr hm_end
                                · bve_jump; exact hJ_oom2 () m_w2 ⟨sf2, hinvf2, htmk2',
                                    by rw [hcv2, hcv1, hcvd, hs2_cv],
                                    by rw [hfl2, hfl1]; exact hfld, hm_w2⟩
                              · bve_jump; exact hJ_oom2 () m_w1 ⟨sf1, hinvf1, htmk1',
                                  by rw [hcv1, hcvd, hs2_cv], by rw [hfl1]; exact hfld, hm_w1⟩
                          · bve_jump; exact hJ_bce () md ⟨sd, hinvd, htmkd, hcvd, hfld, hard, hald,
                              fun idx hi => by rw [hscrd]; exact hbuf_f idx hi, hmd⟩
                        · bve_jump; exact hJ_bce () md ⟨sd, hinvd, htmkd, hcvd, hfld, hard, hald,
                            fun idx hi => by rw [hscrd]; exact hbuf_f idx hi, hmd⟩
                      · -- Optional `full_wstack_defrag`: `if (wcap < wlen || wcap - wlen < w_need)`
                        refine wp_join_group (ts := []) (fun _ mdt => mdt = ml)
                          (fun _ () mdt hmdt => by
                            rcases hmdt.symm with rfl; rw [Blocks.get_here]
                            refine wp_join_group (ts := [])
                              (fun _ md => ∃ sd,
                                FullBveVarSpecs.FullDenseInvW c F0 F_cur sd ∧ TmkInv sd ∧
                                sd.core.cur_vars = s2.core.cur_vars ∧
                                sd.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                                sd.core.arena = s2.core.arena ∧
                                sd.core.arena_len = s2.core.arena_len ∧
                                sd.scratch.scratch_buf = sf.scratch.scratch_buf ∧
                                (FullMem c sd ⋆ R) md)
                              (fun _ () md hmd => by
                                rw [Blocks.get_here]; bve_jump; exact hJdef () md hmd)
                              (fun Jwu hJwu => by
                                bve_ld load_full_wusable hmf
                                bve_jnz hwu_pos
                                · bve_lets
                                  refine wp_call_of_spec _ _ (hDefrag _ _ _ X ?_)
                                  simp only [vals_nil, vals_cons, Arg.val_var]
                                  refine ⟨c, sf, R, rfl, hinvf.1, hinvf.2.1.watches.layout, hmf,
                                    fun wvec' wstk' wlen' wsort' md hlen' hlay' _ hsl' hmd => ?_⟩
                                  dsimp only; bve_jump
                                  exact hJwu () md
                                    ⟨_, bveDenseInvW_of_defrag hinvf hlen' hlay' hsl',
                                    hTmk_cong htmkf rfl rfl, hcvf, hflf, harf, half, rfl, hmd⟩
                                · bve_jump
                                  exact hJwu () ml ⟨sf, hinvf, htmkf, hcvf, hflf, harf, half, rfl,
                                    hmf⟩))
                          (fun Jdt hJdt => by
                            bve_ld load_full_wcap hmf
                            bve_ld load_full_wlen hmf
                            bve_jnz hwc1
                            · bve_jump; exact hJdt () ml rfl
                            · bve_ld load_full_wcap hmf
                              bve_ld load_full_wlen hmf
                              bve_jnz hwc2
                              · bve_jump; exact hJdt () ml rfl
                              · bve_jump
                                exact hJdef () ml ⟨sf, hinvf, htmkf, hcvf, hflf, harf, half, rfl,
                                  hmf⟩)
                  · bve_jump; exact hJ_bce () ml ⟨sf, hinvf, htmkf, hcvf, hflf, harf, half,
                      hbuf_f, hmf⟩
                · bve_jump; exact hJ_bce () ml ⟨sf, hinvf, htmkf, hcvf, hflf, harf, half,
                    hbuf_f, hmf⟩
            · intro J_fit hJ_fit
              bve_jnz hfit0
              · have hsc132 : 132 ≤ c.scratch_cap := by omega
                refine wp_call_of_spec _ _ (hGates _ _ _ _ _ _ X ?_)
                simp only [Arg.val_var]
                refine ⟨c, F0, F_cur, s2, R, rfl, hinv2, hsc132, htmk2, hv_lt, hnp_le, hnn_le,
                  hp_ok, hn_ok, hm2, ?_⟩
                rintro s3 m3 hinv3 htmk3 hcv3 har3 hal3 hfl3 hkeep3 hm3
                have hsc3_len := hinv3.1.scratch_ok.scratch_buf_len
                bve_ld (load_full_scratch_buf (i := 128) (by omega) hm3)
                bve_ld (load_full_scratch_buf (i := 129) (by omega) hm3)
                bve_ld (load_full_scratch_buf (i := 130) (by omega) hm3)
                bve_ld (load_full_scratch_buf (i := 131) (by omega) hm3)
                bve_lets
                refine wp_join_group (ts := [.bool]) (fun (_gf, ()) mgf => mgf = m3) ?_ ?_
                · rintro J_gf ⟨gf, ⟨⟩⟩ mgf h_mgf; subst mgf; rw [Blocks.get_here]; bve_lets
                  refine wp_loop_inv (ts := [i64, i64, .bool, i32])
                    (fun (rc, rp, fit_i, i, _) ml =>
                      ∃ sf, FullBveVarSpecs.FullDenseInvW c F0 F_cur sf ∧ TmkInv sf ∧
                        sf.core.cur_vars = s2.core.cur_vars ∧
                        sf.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                        sf.core.arena = s2.core.arena ∧ sf.core.arena_len = s2.core.arena_len ∧
                        (∀ idx < 128, sf.scratch.scratch_buf[idx]? = scr2[idx]?) ∧
                        i.toNat ≤ np.toNat ∧
                        (fit_i = true → 160 ≤ rp.toNat ∧ rp.toNat ≤ c.scratch_cap ∧
                          FullBveVarSpecs.FullResBufOkW F_cur sf rp.toNat 160) ∧
                        (FullMem c sf ⋆ R) ml)
                    (fun (_, _, fit_i, i, _) _ =>
                      if fit_i then np.toNat - i.toNat + 1 else 0)
                    (fun Jlp hJlp => by
                      bve_jump; rw [hfit0]
                      exact hJlp (0#64, 160#64, true, 0#32, ()) m3
                        ⟨s3, hinv3, htmk3, hcv3, hfl3, har3, hal3, hkeep3, Nat.zero_le _,
                          (fun _ => ⟨by decide,
                            (by rw [show (160#64 : BitVec 64).toNat = 160 from rfl]; omega),
                            (by rw [show (160#64 : BitVec 64).toNat = 160 from rfl]; exact .nil)⟩),
                          hm3⟩)
                    (fun Jlp ⟨rc, rp, fit_i, i, ⟨⟩⟩ ml
                        ⟨sf, hinvf, htmkf, hcvf, hflf, harf, half, hbuf_f, hi_le, hres_f, hml⟩
                        ihlp => by
                      rw [Blocks.get_here]; bve_jnz hi_lt
                      · bve_jnz hfit_i
                        · have hi_nat : i.toNat < np.toNat := by
                            rw [BitVec.ult, decide_eq_true_eq] at hi_lt; exact hi_lt
                          have hhi1 : (i + 1#32).toNat = i.toNat + 1 := by
                            rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
                              Nat.mod_eq_of_lt (by omega : i.toNat + 1 < 2 ^ 32)]
                          refine wp_join_group (ts := [i64, i64, .bool, i32])
                              (fun (rc_n, rp_n, fit_n, _, _) mn =>
                              ∃ sn, FullBveVarSpecs.FullDenseInvW c F0 F_cur sn ∧ TmkInv sn ∧
                                sn.core.cur_vars = s2.core.cur_vars ∧
                                sn.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                                sn.core.arena = s2.core.arena ∧
                                sn.core.arena_len = s2.core.arena_len ∧
                                (∀ idx < 128, sn.scratch.scratch_buf[idx]? = scr2[idx]?) ∧
                                (fit_n = true → 160 ≤ rp_n.toNat ∧ rp_n.toNat ≤ c.scratch_cap ∧
                                  FullBveVarSpecs.FullResBufOkW F_cur sn rp_n.toNat 160) ∧
                                (FullMem c sn ⋆ R) mn) ?_ ?_
                          · rintro Js ⟨rc_n, rp_n, fit_n, _j_n, ⟨⟩⟩ mn
                              ⟨sn, hinvn, htmkn, hcvn, hfln, harn, haln, hbuf_n, hres_n, hmn⟩
                            rw [Blocks.get_here]; bve_jump
                            exact ihlp (rc_n, rp_n, fit_n, i + 1#32, ()) mn (by
                              dsimp only; cases fit_n <;> cases hfit_i <;> simp [hhi1]; omega)
                              ⟨sn, hinvn, htmkn, hcvn, hfln, harn, haln, hbuf_n,
                                by rw [hhi1]; omega, hres_n, hmn⟩
                          · intro Js hJs
                            obtain ⟨hrp_160, hrp_cap, hres_fit⟩ := hres_f hfit_i
                            refine wp_loop_inv (ts := [i64, i64, i32])
                              (fun (rc_j, rp_j, j, _) mj =>
                                ∃ sj, FullBveVarSpecs.FullDenseInvW c F0 F_cur sj ∧ TmkInv sj ∧
                                  sj.core.cur_vars = s2.core.cur_vars ∧
                                  sj.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                                  sj.core.arena = s2.core.arena ∧
                                  sj.core.arena_len = s2.core.arena_len ∧
                                  (∀ idx < 128, sj.scratch.scratch_buf[idx]? = scr2[idx]?) ∧
                                  j.toNat ≤ nn.toNat ∧ 160 ≤ rp_j.toNat ∧
                                  rp_j.toNat ≤ c.scratch_cap ∧
                                  FullBveVarSpecs.FullResBufOkW F_cur sj rp_j.toNat 160 ∧
                                  (FullMem c sj ⋆ R) mj)
                              (fun (_, _, j, _) _ => nn.toNat - j.toNat)
                              (fun Js1 hJs1 => by
                                bve_jump
                                exact hJs1 (rc, rp, 0#32, ()) ml
                                  ⟨sf, hinvf, htmkf, hcvf, hflf, harf, half, hbuf_f, Nat.zero_le _,
                                    hrp_160, hrp_cap, hres_fit, hml⟩)
                              (fun Js1 ⟨rc_j, rp_j, j, ⟨⟩⟩ mj
                                  ⟨sj, hinvj, htmkj, hcvj, hflj, harj, halj, hbuf_j, hj_le,
                                    hrpj_160, hrpj_cap, hres_j, hmj⟩ ihj => by
                                rw [Blocks.get_here]; bve_jnz hj_lt
                                · bve_jnz hfit_j
                                  · have hj_nat : j.toNat < nn.toNat := by
                                      rw [BitVec.ult, decide_eq_true_eq] at hj_lt; exact hj_lt
                                    have hhj1 : (j + 1#32).toNat = j.toNat + 1 := by
                                      rw [BitVec.toNat_add,
                                        show (1#32 : BitVec 32).toNat = 1 from rfl,
                                        Nat.mod_eq_of_lt (by omega : j.toNat + 1 < 2 ^ 32)]
                                    refine wp_join_group (ts := [.bool])
                                      (fun (_need, ()) mnp => mnp = mj) ?_ ?_
                                    · rintro J_np ⟨need_p, ⟨⟩⟩ mnp h_mnp; subst mnp
                                      rw [Blocks.get_here]
                                      refine wp_join_group (ts := [i64, i64, .bool])
                                        (fun (rc_n, rp_n, _fit_n, _) mn =>
                                          ∃ sn, FullBveVarSpecs.FullDenseInvW c F0 F_cur sn ∧
                                            TmkInv sn ∧ sn.core.cur_vars = s2.core.cur_vars ∧
                                            sn.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                                            sn.core.arena = s2.core.arena ∧
                                            sn.core.arena_len = s2.core.arena_len ∧
                                            (∀ idx < 128,
                                              sn.scratch.scratch_buf[idx]? = scr2[idx]?) ∧
                                            160 ≤ rp_n.toNat ∧ rp_n.toNat ≤ c.scratch_cap ∧
                                            FullBveVarSpecs.FullResBufOkW F_cur sn rp_n.toNat 160 ∧
                                            (FullMem c sn ⋆ R) mn) ?_ ?_
                                      · rintro Js2 ⟨rc_n, rp_n, _fit_n, ⟨⟩⟩ mn
                                          ⟨sn, hinvn, htmkn, hcvn, hfln, harn, haln, hbuf_n,
                                            hrpn_160, hrpn_cap, hres_n, hmn⟩
                                        rw [Blocks.get_here]; bve_jump
                                        exact ihj (rc_n, rp_n, j + 1#32, ()) mn
                                          (by dsimp only; rw [hhj1]; omega)
                                          ⟨sn, hinvn, htmkn, hcvn, hfln, harn, haln, hbuf_n,
                                            by rw [hhj1]; omega, hrpn_160, hrpn_cap, hres_n, hmn⟩
                                      · intro Js2 hJs2
                                        bve_jnz hneed
                                        · have hsj_len := hinvj.1.scratch_ok.scratch_buf_len
                                          have hi_eq : (i.setWidth 64).toNat = i.toNat := by
                                            rw [BitVec.toNat_setWidth,
                                              Nat.mod_eq_of_lt (by omega : i.toNat < 2 ^ 64)]
                                          have hi_sj : (i.setWidth 64).toNat <
                                              sj.scratch.scratch_buf.length := by omega
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
                                          bve_ld (c0_load_full_scratch_buf
                                            (i := (64#32 + j).setWidth 64) hj64_sj hmj)
                                          bve_lets
                                          have hwi_j :
                                              sj.scratch.scratch_buf[(i.setWidth 64).toNat]'hi_sj =
                                                scr2[i.toNat]?.getD 0#32 := by
                                            have h0 : sj.scratch.scratch_buf[i.toNat]? =
                                                some (sj.scratch.scratch_buf[(i.setWidth 64).toNat]'
                                                  hi_sj) := by
                                              rw [← hi_eq, List.getElem?_eq_getElem hi_sj]
                                            rw [← h0.symm.trans (hbuf_j i.toNat (by omega))]; rfl
                                          have hwj_j :
                                              sj.scratch.scratch_buf[((64#32 + j).setWidth
                                                  64).toNat]'hj64_sj =
                                                scr2[64 + j.toNat]?.getD 0#32 := by
                                            have h0 : sj.scratch.scratch_buf[64 + j.toNat]? =
                                                some (sj.scratch.scratch_buf[((64#32 + j).setWidth
                                                  64).toNat]'hj64_sj) := by
                                              rw [← hj64_eq, List.getElem?_eq_getElem hj64_sj]
                                            rw [← h0.symm.trans (hbuf_j (64 + j.toNat) (by omega))]
                                            rfl
                                          refine wp_call_of_spec _ _ (hResolve _ _ _ X ?_)
                                          simp only [vals_nil, vals_cons, Arg.val_var]
                                          refine ⟨c, F0, F_cur, sj, R, rfl, hinvj,
                                            (by rw [hcvj, hs2_cv]; exact hv_lt),
                                            (by rw [hwi_j]
                                                exact FullBveVarHelpers.FullBveEntryOkW.with_state
                                                  (by rw [hcvj]; exact Nat.le_refl _) harj halj
                                                  (hp_ok i.toNat hi_nat)),
                                            (by rw [hwj_j]
                                                exact FullBveVarHelpers.FullBveEntryOkW.with_state
                                                  (by rw [hcvj]; exact Nat.le_refl _) harj halj
                                                  (hn_ok j.toNat hj_nat)), hmj, ?_⟩
                                          rintro ok_r lm' tmp' tl' m_r sr hinv_r htl_r hok_rt hm_r
                                          have htmk_r : TmkInv sr := hTmk_cong htmkj rfl rfl
                                          bve_jnz hok_r
                                          · obtain ⟨htl_lits, htl_nd, htl_ent⟩ := hok_rt hok_r
                                            bve_jnz hrc_ov
                                            · bve_jump
                                              exact hJs (rc_j + 1#64, rp_j, false, j, ()) m_r
                                                ⟨sr, hinv_r, htmk_r, hcvj, hflj, harj, halj, hbuf_j,
                                                  (fun h => by cases h), hm_r⟩
                                            · bve_ld load_full_tmp_len hm_r
                                              bve_ld load_full_scratch_cap hm_r
                                              bve_jnz hrp_ov
                                              · bve_jump
                                                exact hJs (rc_j + 1#64, rp_j, false, j, ()) m_r
                                                  ⟨sr, hinv_r, htmk_r, hcvj, hflj, harj, halj,
                                                    hbuf_j, (fun h => by cases h), hm_r⟩
                                              · have htl_lt64 : tl' < 2 ^ 64 := by omega
                                                have htl_lt32 : tl' < 2 ^ 32 := by omega
                                                have hrp_sum_nat :
                                                    (rp_j + 1#64 + BitVec.ofNat 64 tl').toNat =
                                                      rp_j.toNat + 1 + tl' := by
                                                  rw [BitVec.toNat_add, BitVec.toNat_add,
                                                    show (1#64 : BitVec 64).toNat = 1 from rfl,
                                                    BitVec.toNat_ofNat, Nat.mod_eq_of_lt htl_lt64,
                                                    Nat.mod_eq_of_lt
                                                      (by omega : rp_j.toNat + 1 < 2 ^ 64),
                                                    Nat.mod_eq_of_lt
                                                      (by omega : rp_j.toNat + 1 + tl' < 2 ^ 64)]
                                                have hrp_fit :
                                                    rp_j.toNat + 1 + tl' ≤ c.scratch_cap := by
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
                                                let sk0 : FullState := { sr with scratch :=
                                                  { sr.scratch with scratch_buf :=
                                                      (sr.scratch.scratch_buf.set rp_j.toNat
                                                        ((BitVec.ofNat 64 tl').setWidth 32)) } }
                                                have hinv_k0 :
                                                    FullBveVarSpecs.FullDenseInvW c F0 F_cur sk0 :=
                                                  FullBveVarHelpers.FullDenseInvW.with_scratch_buf
                                                    hinv_r (by
                                                      rw [List.length_set]
                                                      exact hinv_r.1.scratch_ok.scratch_buf_len)
                                                bve_ld load_full_tmp_lits_ptr hm_len
                                                refine wp_loop_inv (ts := [i32])
                                                  (fun (k, _) mk =>
                                                    ∃ sk : FullState,
                                                      FullBveVarSpecs.FullDenseInvW c F0 F_cur sk ∧
                                                      TmkInv sk ∧ sk.core = sr.core ∧
                                                      k.toNat ≤ tl' ∧
                                                      (∀ idx < 128,
                                                        sk.scratch.scratch_buf[idx]? = scr2[idx]?) ∧
                                                      (∀ idx < rp_j.toNat,
                                                        sk.scratch.scratch_buf[idx]? =
                                                          sj.scratch.scratch_buf[idx]?) ∧
                                                      (sk.scratch.scratch_buf[rp_j.toNat]?.getD
                                                        0#32).toNat = tl' ∧
                                                      (∀ t < k.toNat,
                                                        sk.scratch.scratch_buf[
                                                          rp_j.toNat + 1 + t]? =
                                                          tmp'[t]?) ∧ (FullMem c sk ⋆ R) mk)
                                                  (fun (k, _) _ => tl' - k.toNat)
                                                  (fun Jk hJk => by
                                                    bve_jump
                                                    exact hJk (0#32, PUnit.unit) m_len
                                                      ⟨sk0, hinv_k0, hTmk_cong htmk_r rfl rfl, rfl,
                                                        Nat.zero_le _,
                                                        (fun idx hi => by
                                                          dsimp only [sk0]
                                                          rw [List.getElem?_set_ne (by omega)]
                                                          exact hbuf_j idx hi),
                                                        (fun idx hi => by
                                                          dsimp only [sk0]
                                                          rw [List.getElem?_set_ne (by omega)]),
                                                        (by dsimp only [sk0]
                                                            rw [List.getElem?_set_self hrp_lt_scr,
                                                              Option.getD_some,
                                                              BitVec.toNat_setWidth,
                                                              BitVec.toNat_ofNat,
                                                              Nat.mod_eq_of_lt htl_lt64,
                                                              Nat.mod_eq_of_lt htl_lt32]),
                                                        (fun _ ht => absurd ht (Nat.not_lt_zero _)),
                                                        hm_len⟩)
                                                  (fun Jk ⟨k, ⟨⟩⟩ mk
                                                      ⟨sk, hinv_k, htmk_k, hcore_k, hk_le,
                                                        hbuf_k128, hbuf_krp, hsz_k, hcp_k, hmk⟩
                                                      ihk => by
                                                    rw [Blocks.get_here]
                                                    bve_ld load_full_tmp_len hmk
                                                    bve_jnz hk_lt
                                                    · have hk_eq :
                                                          (k.setWidth 64).toNat = k.toNat := by
                                                        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt
                                                          (by have := k.isLt; omega)]
                                                      have hk_nat : k.toNat < tl' := by
                                                        have h0 : BitVec.ult (k.setWidth 64)
                                                            (BitVec.ofNat 64 sk.core.tmp_len) =
                                                            true := hk_lt
                                                        rw [hcore_k] at h0
                                                        rw [BitVec.ult, decide_eq_true_eq, hk_eq,
                                                          BitVec.toNat_ofNat,
                                                          Nat.mod_eq_of_lt htl_lt64] at h0
                                                        exact h0
                                                      have hk_tmp : (k.setWidth 64).toNat <
                                                          sk.core.tmp.length := by
                                                        rw [hk_eq, hinv_k.1.core_ok.tmp_len_arr]
                                                        exact Nat.lt_of_lt_of_le hk_nat
                                                          (Nat.le_trans htl_r
                                                            (by rw [hcvj]; exact hcv_le))
                                                      have hk_scr_nat :
                                                          (rp_j + 1#64 + k.setWidth 64).toNat =
                                                            rp_j.toNat + 1 + k.toNat := by
                                                        rw [BitVec.toNat_add, BitVec.toNat_add,
                                                          show (1#64 : BitVec 64).toNat = 1
                                                            from rfl,
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
                                                          (sk.core.tmp[
                                                            (k.setWidth 64).toNat]'hk_tmp)
                                                          hk_scr hmk
                                                      bve_jump
                                                      let sk1 : FullState := { sk with scratch :=
                                                        { sk.scratch with scratch_buf :=
                                                            (sk.scratch.scratch_buf.set
                                                              (rp_j + 1#64 + k.setWidth 64).toNat
                                                              (sk.core.tmp[(k.setWidth 64).toNat]'
                                                                hk_tmp)) } }
                                                      have hinv_k1 :
                                                          FullBveVarSpecs.FullDenseInvW c F0 F_cur
                                                            sk1 :=
                                                        FullDenseInvW.with_scratch_buf (s := sk)
                                                          hinv_k (by
                                                            have hlen_s :=
                                                              hinv_k.1.scratch_ok.scratch_buf_len
                                                            rw [List.length_set]; exact hlen_s)
                                                      have hk1 : (k + 1#32).toNat = k.toNat + 1 :=
                                                        by rw [BitVec.toNat_add,
                                                            show (1#32 : BitVec 32).toNat = 1 from
                                                              rfl,
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
                                                        ⟨sk1, hinv_k1, hTmk_cong htmk_k rfl rfl,
                                                          hcore_k, by rw [hk1]; omega,
                                                          (fun idx hi => by
                                                            dsimp only [sk1]
                                                            rw [List.getElem?_set_ne
                                                              (by rw [hk_scr_nat]; omega)]
                                                            exact hbuf_k128 idx hi),
                                                          (fun idx hi => by
                                                            dsimp only [sk1]
                                                            rw [List.getElem?_set_ne
                                                              (by rw [hk_scr_nat]; omega)]
                                                            exact hbuf_krp idx hi),
                                                          (by dsimp only [sk1]
                                                              rw [List.getElem?_set_ne
                                                                (by rw [hk_scr_nat]; omega)]
                                                              exact hsz_k),
                                                          (fun t ht => by
                                                            rw [hk1] at ht; dsimp only [sk1]
                                                            rcases Nat.lt_or_eq_of_le
                                                                (Nat.lt_succ_iff.mp ht) with
                                                                hlt | rfl
                                                            · rw [List.getElem?_set_ne
                                                                (by rw [hk_scr_nat]; omega)]
                                                              exact hcp_k t hlt
                                                            · rw [hk_scr_nat,
                                                                List.getElem?_set_self (by
                                                                  rw [← hk_scr_nat]; exact hk_scr)]
                                                              exact hval_k), hm_k1⟩
                                                    · have hk_eq_tl : k.toNat = tl' := by
                                                        have h0 : BitVec.ult (k.setWidth 64)
                                                            (BitVec.ofNat 64 sk.core.tmp_len) =
                                                            false := hk_lt
                                                        rw [hcore_k] at h0
                                                        rw [BitVec.ult, decide_eq_false_iff_not,
                                                          BitVec.toNat_setWidth,
                                                          Nat.mod_eq_of_lt (by
                                                            have := k.isLt
                                                            omega : k.toNat < 2 ^ 64),
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
                                                        exact Nat.le_trans htl_r
                                                          (by rw [hcvj]; exact hcv_le)
                                                      have hcp_tl : ∀ t < tl',
                                                          sk.scratch.scratch_buf[rp_j.toNat + 1 +
                                                            t]? = tmp'[t]? :=
                                                        fun t ht => hcp_k t (by omega)
                                                      have hres_sk :
                                                          FullBveVarSpecs.FullResBufOkW F_cur sk
                                                            (rp_j + 1#64 +
                                                              BitVec.ofNat 64 sk.core.tmp_len).toNat
                                                            160 := by
                                                        rw [hcore_k]
                                                        change FullBveVarSpecs.FullResBufOkW F_cur
                                                          sk (rp_j + 1#64 + BitVec.ofNat 64
                                                            tl').toNat 160
                                                        rw [hrp_sum_nat]
                                                        refine
                                                          FullResBufOkW.append_block
                                                            (s := sj) (s' := sk) (r0 := 160)
                                                            (r1 := rp_j.toNat) (sz := tl')
                                                            (by rw [hcore_k]) hbuf_krp hsz_k ?_ ?_
                                                            ?_ hres_j
                                                        · intro t ht; rw [hcp_tl t ht, hcore_k]
                                                          exact htl_lits t ht
                                                        · rw [range_map_div2_eq_take_map
                                                            htmp_tl hcp_tl]
                                                          exact htl_nd
                                                        · rw [range_map_eq_take_map htmp_tl hcp_tl]
                                                          exact htl_ent
                                                      exact hJs2 (rc_j + 1#64,
                                                          rp_j + 1#64 +
                                                            BitVec.ofNat 64 sk.core.tmp_len,
                                                          fit_i, ()) mk
                                                        ⟨sk, hinv_k, htmk_k,
                                                          by rw [hcore_k]; exact hcvj,
                                                          by rw [hcore_k]; exact hflj,
                                                          by rw [hcore_k]; exact harj,
                                                          by rw [hcore_k]; exact halj, hbuf_k128,
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
                                              ⟨sr, hinv_r, htmk_r, hcvj, hflj, harj, halj, hbuf_j,
                                                hrpj_160, hrpj_cap,
                                                FullBveVarHelpers.FullResBufOkW.with_state
                                                  (s := sj) (s' := sr) rfl (fun _ _ => rfl) hres_j,
                                                hm_r⟩
                                        · bve_jump
                                          exact hJs2 (rc_j, rp_j, fit_i, ()) mj
                                            ⟨sj, hinvj, htmkj, hcvj, hflj, harj, halj, hbuf_j,
                                              hrpj_160, hrpj_cap, hres_j, hmj⟩
                                    · intro J_np hJ_np
                                      bve_jnz hgf_not
                                      · bve_jnz hbit
                                        · bve_jump; exact hJ_np (true, ()) mj rfl
                                        · bve_jump; exact hJ_np (false, ()) mj rfl
                                      · bve_jump; exact hJ_np (true, ()) mj rfl
                                  · exact absurd hfit_j (by rw [hfit_i]; decide)
                                · bve_jump
                                  exact hJs (rc_j, rp_j, fit_i, j, ()) mj
                                    ⟨sj, hinvj, htmkj, hcvj, hflj, harj, halj, hbuf_j,
                                      (fun _ => ⟨hrpj_160, hrpj_cap, hres_j⟩), hmj⟩)
                        · bve_jump
                          exact hJ_fit (rc, rp, fit_i, ()) ml
                            ⟨sf, hinvf, htmkf, hcvf, hflf, harf, half, hbuf_f, hres_f, hml⟩
                      · bve_jump
                        exact hJ_fit (rc, rp, fit_i, ()) ml
                          ⟨sf, hinvf, htmkf, hcvf, hflf, harf, half, hbuf_f, hres_f, hml⟩)
                · intro J_gf hJ_gf
                  bve_jnz hpm
                  · bve_jump; exact hJ_gf (true, ()) m3 rfl
                  · bve_jnz hnm
                    · bve_jump; exact hJ_gf (true, ()) m3 rfl
                    · bve_jump; exact hJ_gf (false, ()) m3 rfl
              · bve_jump; rw [hfit0]; exact hJ_fit (0#64, 160#64, false, PUnit.unit) m2
                  ⟨s2, hinv2, htmk2, rfl, Nat.le_refl _, rfl, rfl, (fun _ _ => rfl),
                    (fun h => by cases h), hm2⟩
          · intro J hJ
            have hpure := m5_bve_pure_elim_wp (X := X) (J := J)
              (nl := pl ||| 1#32)
              (ext_ok := (BitVec.ofNat 64 s2.scratch.extend_len + (en1 + en2)).ule
                (BitVec.ofNat 64 c.extend_cap))
              Γ TmkInv hTmk_cong hWeaken hSetInact hv_lt hpl_nat hnl_nat hnp_le hnn_le hsc512
              hinv2 htmk2 hs2_cv hs2_fl hp_ok hn_ok hm2 (hJ () m2 rfl) hQ
            unfold m5BvePureElimExpr at hpure
            exact hpure

end BveVarHelpers

/-! ## 3. Public Canonical & `TmkZero` Specs (`full_bve_var_m5_wp`, `full_bve_var_m5_def_wp`) -/

/-- Canonical `Full.fullBveVarSpec` proof for `full_bve_var_m5`. -/
public theorem full_bve_var_m5_wp (Γ : Env)
    (hDefrag : ∀ xs m Q X, fullWstackDefragSpec xs m Q X →
      Γ "full_wstack_defrag" [i64] [] xs m Q X)
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
    ∀ args m Q X, Full.fullBveVarSpec args m Q X →
      Func.wp Γ full_bve_var_m5_body args m Q X := by
  rintro ⟨h, v, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hdense, hv_lt, hm, hQ⟩
  refine m5_bve_var_core_wp Γ (fun _ => True) (fun _ _ _ => trivial) hDefrag hCollect hExtNeed
    (fun h blk off cnt m0 Q0 X0 ⟨c0, F00, Fc0, s0, R0, hh, hd0, _, hblk, hoff, hw, hm0, hQ0⟩ =>
      hWeaken _ m0 Q0 X0 ⟨c0, F00, Fc0, s0, R0, hh, hd0, hblk, hoff, hw, hm0,
        fun ok s' m' h1 h2 h3 h4 h5 hm' => hQ0 ok s' m' h1 trivial h2 h3 h4 h5 hm'⟩)
    (bve_setInact_adapter hSetInact)
    (fun h v0 np0 nn0 m0 Q0 X0 ⟨c0, F00, Fc0, s0, R0, hh, hd0, hsc0, _, hv0, hnp0, hnn0, hp, hn,
        hm0, hQ0⟩ =>
      hGates _ m0 Q0 X0 ⟨c0, F00, Fc0, s0, R0, hh, hd0, hsc0, hv0, hnp0, hnn0, hp, hn, hm0,
        fun lm' scr' m' hd' hkp' hm' => hQ0 _ m' hd' trivial rfl rfl rfl (Nat.le_refl _)
          (fun i hi => hkp' i (by omega) (Or.inl hi)) hm'⟩)
    hResolve
    (fun h r_off r_end m0 Q0 X0 ⟨c0, F00, Fc0, s0, R0, hh, hd0, _, hle, hcap, hbuf, hm0, hQ0⟩ =>
      hCommitRes _ m0 Q0 X0 ⟨c0, F00, Fc0, s0, R0, hh, hd0, hle, hcap, bve_resBuf_of_bve hbuf, hm0,
        fun r s' m' h1 h2 h3 h4 h5 hm' => hQ0 r s' m' h1 trivial h2 h3 h4 h5 hm'⟩)
    (bve_tryBce_adapter hTryBce)
    (fun h blk ot m0 Q0 X0 ⟨c0, s0, R0, hpre, hlen0, _, hm0, hQ0⟩ =>
      hExtPush2 _ m0 Q0 X0 ⟨c0, s0, R0, hpre, hlen0, hm0,
        fun r s' m' hag hlen' hpost hm' => hQ0 r s' m' hag hlen' hpost trivial hm'⟩)
    hDelBin
    (fun h blk cr m0 Q0 X0 ⟨c0, s0, R0, hpre, hlen0, _, hm0, hQ0⟩ =>
      hExtPushCl _ m0 Q0 X0 ⟨c0, s0, R0, hpre, hlen0, hm0,
        fun r s' m' hag hlen' hpost hm' => hQ0 r s' m' hag hlen' hpost trivial hm'⟩)
    hdense trivial hv_lt hm
    (fun r s' m' hd' _ hcv hfl hr h20 hm' => hQ r s' m' hd' hcv hfl hr h20 hm')

/-- M2 `FullDefSweep`-compatible `fullBveVarDefSpec` proof for `full_bve_var_m5`. -/
public theorem full_bve_var_m5_def_wp (Γ : Env)
    (hDefrag : ∀ xs m Q X, fullWstackDefragSpec xs m Q X →
      Γ "full_wstack_defrag" [i64] [] xs m Q X)
    (hCollect : ∀ xs m Q X, fullBveCollectSpec xs m Q X →
      Γ "full_bve_collect" [i64, i32, i64, i32] [i32] xs m Q X)
    (hExtNeed : ∀ xs m Q X, fullBveExtNeedSpec xs m Q X →
      Γ "full_bve_ext_need" [i64, i32, i32] [i64] xs m Q X)
    (hWeaken : ∀ xs m Q X, fullBveWeakenTmkSpec xs m Q X →
      Γ "full_bve_weaken" [i64, i32, i32, i32] [.bool] xs m Q X)
    (hSetInact : ∀ xs m Q X, fullSetInactiveSpec xs m Q X →
      Γ "full_set_inactive" [i64, i32, i32] [] xs m Q X)
    (hGates : ∀ xs m Q X, fullBveGatesDefFastSpec xs m Q X →
      Γ "full_bve_gates" [i64, i32, i32, i32] [] xs m Q X)
    (hResolve : ∀ xs m Q X, fullBveResolvePairSpec xs m Q X →
      Γ "full_bve_resolve_pair" [i64, i32, i32, i32] [.bool] xs m Q X)
    (hCommitRes : ∀ xs m Q X, fullBveCommitResTmkSpec xs m Q X →
      Γ "full_bve_commit_res" [i64, i64, i64] [i64] xs m Q X)
    (hTryBce : ∀ xs m Q X, fullBveTryBceSpec xs m Q X →
      Γ "full_bve_try_bce" [i64, i32, i32, i32, i32] [.bool] xs m Q X)
    (hExtPush2 : ∀ xs m Q X, fullExtendPush2TmkSpec xs m Q X →
      Γ "full_extend_push2" [i64, i32, i32] [.bool] xs m Q X)
    (hDelBin : ∀ xs m Q X, fullDeleteBinarySpec xs m Q X →
      Γ "full_delete_binary" [i64, i32, i32] [] xs m Q X)
    (hExtPushCl : ∀ xs m Q X, fullExtendPushClTmkSpec xs m Q X →
      Γ "full_extend_push_cl" [i64, i32, i32] [.bool] xs m Q X) :
    ∀ args m Q X, fullBveVarDefSpec args m Q X →
      Func.wp Γ full_bve_var_m5_body args m Q X := by
  rintro ⟨h, v, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hdense, htmk, hv_lt, hm, hQ⟩
  refine m5_bve_var_core_wp Γ TmkZero (fun h hcv ht => h.congr hcv ht) hDefrag hCollect hExtNeed
    (fun h blk off cnt m0 Q0 X0 ⟨c0, F00, Fc0, s0, R0, hh, hd0, htm0, hblk, hoff, hw, hm0, hQ0⟩ =>
      hWeaken _ m0 Q0 X0 ⟨c0, F00, Fc0, s0, R0, hh, hd0, htm0, hblk, hoff, hw, hm0, hQ0⟩)
    (bve_setInact_adapter hSetInact)
    (fun h v0 np0 nn0 m0 Q0 X0 ⟨c0, F00, Fc0, s0, R0, hh, hd0, hsc0, htm0, hv0, hnp0, hnn0,
        hp, hn, hm0, hQ0⟩ =>
      hGates _ m0 Q0 X0 ⟨c0, F00, Fc0, s0, R0, hh, hd0, hsc0, htm0, hv0, hnp0, hnn0, hp, hn, hm0,
        fun s' m' hd' htm' hcv' har' hal' hfl' hkp' _ hm' =>
          hQ0 s' m' hd' htm' hcv' har' hal' hfl' hkp' hm'⟩)
    hResolve
    (fun h r_off r_end m0 Q0 X0 ⟨c0, F00, Fc0, s0, R0, hh, hd0, htm0, hle, hcap, hbuf, hm0, hQ0⟩ =>
      hCommitRes _ m0 Q0 X0
        ⟨c0, F00, Fc0, s0, R0, hh, hd0, htm0, hle, hcap, bve_resBuf_of_bve hbuf, hm0, hQ0⟩)
    (bve_tryBce_adapter hTryBce)
    (fun h blk ot m0 Q0 X0 ⟨c0, s0, R0, hpre, hlen0, htm0, hm0, hQ0⟩ =>
      hExtPush2 _ m0 Q0 X0 ⟨c0, s0, R0, hpre, hlen0, hm0,
        fun r s' m' hag hlen' ⟨hll, hex, hscr, htmk_eq⟩ hm' =>
          hQ0 r s' m' hag hlen' ⟨hll, hex, hscr⟩
            (htm0.congr (congrArg FullCoreState.cur_vars (fullCoreState_agrees_with_scratch hag))
              htmk_eq) hm'⟩)
    hDelBin
    (fun h blk cr m0 Q0 X0 ⟨c0, s0, R0, hpre, hlen0, htm0, hm0, hQ0⟩ =>
      hExtPushCl _ m0 Q0 X0 ⟨c0, s0, R0, hpre, hlen0, hm0,
        fun r s' m' hag hlen' ⟨hll, hex, hscr, htmk_eq⟩ hm' =>
          hQ0 r s' m' hag hlen' ⟨hll, hex, hscr⟩
            (htm0.congr (congrArg FullCoreState.cur_vars (fullCoreState_agrees_with_scratch hag))
              htmk_eq) hm'⟩)
    hdense htmk hv_lt hm hQ

end LeanQbe.T.Examples.Kissat.FullM5DenseSafe
