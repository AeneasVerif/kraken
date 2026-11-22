module

public import LeanQbe.T.Examples.Kissat.PlainSpec
import LeanQbe.T.Examples.Kissat.DimacsLemmas
import LeanQbe.T.Logic.C0Step
public meta import Lean.Elab.Tactic
public meta import LeanQbe.T.Logic.C0Step

/-!
# Soundness Proofs for Kissat `D-Plain` Clause Addition, Skip & Ingestion (`Stage 3`, Part 1)

Proves `Func.wp` specifications for:
1. `plain_add_clause` (`plainAddClauseSpec`, `plain_add_clause_wp`)
2. `plain_skip_cl` (`plainSkipClSpec`, `plain_skip_cl_wp`)
3. `plain_ingest_cl` (`plainIngestClSpec`, `plain_ingest_cl_wp`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Plain

open Std Std.Sat Std.ExtHashMap LeanQbe.T.C0Step
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

namespace PlainIngestTactics

theorem bv64_shl1_nat_eq {n : Nat} :
    BitVec.ofNat 64 n <<< (1 : Nat) = BitVec.ofNat 64 (2 * n) := by bv_omega

theorem bv32_lshr1 (x : BitVec 32) : (x >>> (1 : Nat)).toNat = x.toNat / 2 := bv32_lshr_1 x

theorem bv32_beq_nat_eq {n : Nat} {x : BitVec 32} (hn : n < 2 ^ 32) :
    (x == BitVec.ofNat 32 n) = decide (x.toNat = n) := by
  by_cases h : x.toNat = n
  · have hx : x = BitVec.ofNat 32 n :=
      BitVec.eq_of_toNat_eq (by rw [bv32_ofNat_toNat hn]; exact h)
    simp [hx, bv32_ofNat_toNat hn]
  · have hx : x ≠ BitVec.ofNat 32 n := fun he =>
      h (by simpa [bv32_ofNat_toNat hn] using congrArg BitVec.toNat he)
    simp [h, hx]

theorem bv64_beq_eq {x y : BitVec 64} : (x == y) = decide (x = y) := by
  by_cases h : x = y <;> simp [h]

theorem i8_vals_beq0 {x : BitVec 8} (hx : x = 0#8 ∨ x = 1#8 ∨ x = 0xFF#8) :
    (x.signExtend 32 == 0#32) = decide (x = 0#8) := by
  rcases hx with rfl | rfl | rfl <;> decide

theorem bv32_tag_bin_flag (x : BitVec 32) :
    (((x &&& 0x7FFFFFFF#32) ||| 0x80000000#32) &&& 0x80000000#32) ≠ 0#32 := by
  intro he; have h31 := congrArg (fun v : BitVec 32 => v.getLsbD 31) he; simp at h31

theorem bv32_tag_bin_mask {x : BitVec 32} (hx : x.toNat < 2 ^ 30) :
    (((x &&& 0x7FFFFFFF#32) ||| 0x80000000#32) &&& 0x7FFFFFFF#32) = x := by
  have hm : (x &&& 0x7FFFFFFF#32) = x := BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_and, show (0x7FFFFFFF#32).toNat = 2 ^ 31 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)])
  rw [← hm]; apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or]
  have h1 : !((0x80000000#32).getLsbD i && (0x7FFFFFFF#32).getLsbD i) := by revert i hi; decide
  cases h8 : (0x80000000#32).getLsbD i <;> simp_all

theorem bv32_tag_bin_ne_sent {x : BitVec 32} (hx : x.toNat < 2 ^ 30) :
    ((x &&& 0x7FFFFFFF#32) ||| 0x80000000#32) ≠ 0xFFFFFFFF#32 := by
  intro he; have h30 := congrArg (fun v : BitVec 32 => v.getLsbD 30) he
  have hx30 : x.getLsbD 30 = false := by
    rw [BitVec.getLsbD_eq_getElem (by decide), BitVec.getElem_eq_testBit_toNat]
    exact Nat.testBit_lt_two_pow hx
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, hx30, Bool.false_and] at h30; revert h30; decide

theorem bv32_mask_flag0 (x : BitVec 32) : ((x &&& 0x7FFFFFFF#32) &&& 0x80000000#32) = 0#32 := by
  rw [BitVec.and_assoc, show (0x7FFFFFFF#32 &&& 0x80000000#32) = 0#32 by decide, BitVec.and_zero]

theorem bv32_mask_ne_sent (x : BitVec 32) : (x &&& 0x7FFFFFFF#32) ≠ 0xFFFFFFFF#32 := by
  intro he; have h31 := congrArg (fun v : BitVec 32 => v.getLsbD 31) he; simp at h31

theorem bv32_or_garb_noshrk {x : BitVec 32} (hx : (x &&& 0x00800000#32) = 0#32) :
    ((x ||| 0x00080000#32) &&& 0x00800000#32) = 0#32 := by
  rw [← hx]; apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or]
  have h1 : !((0x00080000#32).getLsbD i && (0x00800000#32).getLsbD i) := by revert i hi; decide
  cases h8 : (0x00080000#32).getLsbD i <;> simp_all

theorem bv32_or_garb_nz (x : BitVec 32) : ((x ||| 0x00080000#32) &&& 0x00080000#32) ≠ 0#32 := by
  intro he; have h19 := congrArg (fun v : BitVec 32 => v.getLsbD 19) he; simp at h19

theorem bv32_ptag_ofNat {l : Nat} (hl : l < 2 ^ 32) :
    BitVec.setWidth 8 ((BitVec.ofNat 32 l &&& (1 : BitVec 32)) + (1 : BitVec 32)) =
      BitVec.ofNat 8 (l % 2 + 1) := by
  apply BitVec.eq_of_toNat_eq
  have hand : (BitVec.ofNat 32 l &&& (1 : BitVec 32)).toNat = l % 2 := by
    rw [BitVec.toNat_and, show (1 : BitVec 32).toNat = 1 from rfl,
      show (BitVec.ofNat 32 l).toNat = l from Nat.mod_eq_of_lt hl, Nat.and_one_is_mod]
  rw [BitVec.toNat_setWidth, BitVec.toNat_add, hand, show (1 : BitVec 32).toNat = 1 from rfl,
    Nat.mod_eq_of_lt (by omega : l % 2 + 1 < 2 ^ 32)]
  simp [Nat.mod_eq_of_lt (by omega : l % 2 + 1 < 2 ^ 8)]

theorem bv8_zext32_eq_zero {a : BitVec 8} : a.setWidth 32 = 0#32 ↔ a = 0#8 :=
  bv8_zext32_eq (b := 0#8)

theorem bv8_zext32_bne {a b : BitVec 8} :
    (a.setWidth 32 != b.setWidth 32) = decide (a ≠ b) := by
  by_cases h : a = b <;> simp [bne, h, bv8_zext32_eq]

theorem p_strip_wp {Γ rs Q X e m} (h : wp (rs := rs) Γ Q X e m) : wp Γ Q X e m := h
theorem p_strip_fwp {as rs Γ f args m Q X}
    (h : Func.wp (as := as) (rs := rs) Γ f args m Q X) : Func.wp Γ f args m Q X := h
theorem p_strip_le_wp {a b : Nat} {P : Prop} (h : a ≤ b) (hp : P) : a ≤ b ∧ P := ⟨h, hp⟩

scoped macro "p_lets" : tactic => `(tactic| (
  (try (first | refine p_strip_fwp ?_ | refine p_strip_wp ?_))
  (try c0_let_simp); repeat (refine p_strip_le_wp (by decide) ?_; try c0_let_simp)))

theorem wp_head_jnz_iff {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {c : Arg Val .bool} {b : Bool} {t e : Expr Val Cont rs} (hc : c.val = b)
    (h : (b = true → wp Γ Q X t m) ∧ (b = false → wp Γ Q X e m)) :
    wp Γ Q X (.jnz c t e) m := by subst hc; rw [wp_jnz]; exact h

scoped macro "c0_val_eq" : tactic => `(tactic| (
  (try simp only [liftCmp, Ty.hasFloat, Arg.val_var, Arg.val_imm, Prod.fst, Prod.snd,
    evalBits_eq_beq, evalBits_ne_bne, evalBits_ult_eq, evalBits_ule_eq, evalBits_ugt_eq,
    evalBits_uge_eq, evalBits_slt_eq, evalBits_sle_eq, evalBits_sgt_eq, evalBits_sge_eq,
    Bool.not_true, Bool.not_false,
    BitVec.reduceSignExtend, BitVec.reduceSetWidth, BitVec.reduceAdd, BitVec.reduceMul]);
  all_goals rfl))

section BvC0Extras
@[scoped bv_c0] theorem bv32_toNat_0 : (0 : BitVec 32).toNat = 0 := rfl
@[scoped bv_c0] theorem bv32_toNat_1 : (1 : BitVec 32).toNat = 1 := rfl
@[scoped bv_c0] theorem bv64_toNat_0 : (0 : BitVec 64).toNat = 0 := rfl
@[scoped bv_c0] theorem bv64_toNat_1 : (1 : BitVec 64).toNat = 1 := rfl
@[scoped bv_c0] theorem bv_c0_xor1 (n : Nat) : n ^^^ 1 = n + 1 - 2 * (n % 2) := by
  have h := litNeg_eq n; unfold litNeg at h; rw [h]; split <;> omega
@[scoped bv_c0] theorem cfg_mv_mod (c : PlainCfg) : c.mv % 2 ^ 64 = c.mv := by
  have := c.hmv; unfold dimacsBound at this; exact Nat.mod_eq_of_lt (by omega)
@[scoped bv_c0] theorem cfg_nc_mod (c : PlainCfg) : c.nc % 2 ^ 64 = c.nc := by
  have := c.hnc; unfold dimacsBound at this; exact Nat.mod_eq_of_lt (by omega)
@[scoped bv_c0] theorem cfg_arena_cap_mod (c : PlainCfg) : c.arena_cap % 2 ^ 64 = c.arena_cap := by
  have := c.harena; unfold dimacsBound at this; exact Nat.mod_eq_of_lt (by omega)
@[scoped bv_c0] theorem cfg_wcap_mod (c : PlainCfg) : c.wcap % 2 ^ 64 = c.wcap := by
  have := c.hwcap; unfold dimacsBound at this; exact Nat.mod_eq_of_lt (by omega)
@[scoped bv_c0] theorem bv32_toNat_mod64 (x : BitVec 32) : x.toNat % 2 ^ 64 = x.toNat :=
  Nat.mod_eq_of_lt (by have := x.isLt; omega)
@[scoped bv_c0] theorem bv32_div2_mod64 (x : BitVec 32) : (x.toNat / 2) % 2 ^ 64 = x.toNat / 2 :=
  Nat.mod_eq_of_lt (by have := x.isLt; omega)
@[scoped bv_c0] theorem bv64_toNat_mod64 (x : BitVec 64) : x.toNat % 2 ^ 64 = x.toNat :=
  Nat.mod_eq_of_lt x.isLt
theorem bv64_setWidth32_ofNat (x : Nat) :
    BitVec.setWidth 32 (BitVec.ofNat 64 x) = BitVec.ofNat 32 x := BitVec.eq_of_toNat_eq (by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; exact Nat.mod_mod_of_dvd _ (by decide))
theorem bv64_add1_toNat {n : Nat} (h : n + 1 < 2 ^ 64) : (BitVec.ofNat 64 n + 1).toNat = n + 1 := by
  rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add, bv64_ofNat_toNat h]
attribute [scoped bv_c0] BitVec.toNat_ushiftRight BitVec.toNat_shiftLeft BitVec.toNat_xor
  BitVec.toNat_and Nat.shiftLeft_eq Nat.shiftRight_eq_div_pow List.length_set List.length_replicate
attribute [scoped bv_c0 high] LeanQbe.T.bv_c0_zext32_64 LeanQbe.T.bv_c0_zext8_64
  LeanQbe.T.bv_c0_zext8_32
@[scoped c0_load] theorem c0_load_arena_tmp0 {c : PlainCfg} {s : PlainState} {R : Mem 64 → Prop}
    {m : Mem 64} (hi : 0 < s.tmp.length) (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i32 (c.pTmp + 0#64) = some s.tmp[0] := load_arena_tmp (i := 0) hi hm
@[scoped c0_load] theorem c0_load_arena_tmp1 {c : PlainCfg} {s : PlainState} {R : Mem 64 → Prop}
    {m : Mem 64} (hi : 1 < s.tmp.length) (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i32 (c.pTmp + 4#64) = some s.tmp[1] := load_arena_tmp (i := 1) hi hm
end BvC0Extras

scoped elab "pi_unmdata" : tactic => Lean.Elab.Tactic.liftMetaTactic1 fun g => do
  let ty ← Lean.instantiateMVars (← g.getType)
  if ty.isMData then return some (← g.replaceTargetDefEq ty.consumeMData) else return some g

scoped elab "pi_head_steps" : tactic => do
  let isBranchHead (ty : Lean.Expr) : Bool :=
    let ty := ty.consumeMData.headBeta
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 then
      let e := (ty.getArg! 4).consumeMData.headBeta
      e.isAppOf ``LeanQbe.T.Expr.jnz || e.isAppOf ``LeanQbe.T.Expr.group
    else false
  let unwrapMData (g : Lean.MVarId) : Lean.MetaM Lean.MVarId := do
    let ty0 ← Lean.instantiateMVars (← g.getType)
    let g ← if ty0.isMData then g.replaceTargetDefEq ty0.consumeMData else pure g
    let ty := (← Lean.instantiateMVars (← g.getType)).headBeta
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 then
      let e := ty.getArg! 4
      if e.isMData then
        return ← g.replaceTargetDefEq
          (Lean.mkAppN ty.getAppFn (ty.getAppArgs.set! 4 e.consumeMData))
    return g
  for _ in [:450] do
    let gs ← Lean.Elab.Tactic.getUnsolvedGoals
    let some g := gs.head? | break
    let g ← unwrapMData g
    if isBranchHead (← Lean.instantiateMVars (← g.getType)) then
      Lean.Elab.Tactic.setGoals (g :: gs.tail!); break
    Lean.Elab.Tactic.setGoals [g]
    let s ← Lean.Elab.Tactic.saveState
    let ok ← try stepOnce catch _ => s.restore; pure false
    Lean.Elab.Tactic.setGoals ((← Lean.Elab.Tactic.getUnsolvedGoals) ++ gs.tail!)
    if !ok then break

scoped macro "pi_clean" : tactic => `(tactic| simp only [Nat.reduceLeDiff, Nat.le_refl, true_and,
  and_true, Bool.false_or, Bool.or_false, Bool.true_and, Bool.and_true, Bool.not_true,
  Bool.not_false, decide_eq_true_eq, decide_eq_false_iff_not])

scoped macro "pi_steps" : tactic => `(tactic| (
  all_goals try pi_unmdata; c0_steps
  repeat (any_goals pi_clean; all_goals try pi_unmdata; c0_steps)))

end PlainIngestTactics

open scoped PlainIngestTactics
open PlainIngestTactics

/-! ## 1. `plain_add_clause` -/

private theorem entails_bin_swap {F0 : CNF Nat} {a b : Nat}
    (h : F0.EntailsClause (cnfClause [a, b])) : F0.EntailsClause (cnfClause [b, a]) :=
  entails_of_mem_or_false h fun _ hm => Or.inl (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢; exact hm.elim Or.inr Or.inl)

theorem plain_add_clause_wp (Γ : Env)
    (hAlloc : ∀ args m Q X, plainAllocClSpec args m Q X →
      Γ "plain_alloc_cl" [i64, i32, i32, .bool] [i64] args m Q X)
    (hPush : ∀ args m Q X, plainWatchPushSpec args m Q X →
      Γ "plain_watch_push" [i64, i32, i32, i32, i32] [.bool] args m Q X) :
    ∀ args m Q X, plainAddClauseSpec args m Q X → Func.wp Γ plain_add_clause_body args m Q X := by
  rintro ⟨h, len, glue, red, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hcore, hlen_le, hcl_bd, hm, hQ⟩
  have hmv := c.hmv; have har := c.harena; have hw := c.hwcap
  unfold dimacsBound at hmv har hw; have hlen := hcore.lengths
  pi_head_steps
  refine wp_head_jnz_iff (b := decide (len.toNat = 2))
    (by simpa [Arg.val_var] using bv32_beq_nat_eq (x := len) (n := 2) (by decide)) ?_
  rw [decide_eq_true_eq, decide_eq_false_iff_not]; refine ⟨fun h2 => ?_, fun hne2 => ?_⟩
  · simp only [h2, show ¬ (2 < 2) by omega, ↓reduceIte] at hQ hcl_bd
    obtain ⟨hlits_lt, hent2⟩ := hcl_bd (by omega)
    have htm_gt0 : 0 < s.tmp.length := by rw [hlen.tmp_len_arr]; omega
    have htm_gt1 : 1 < s.tmp.length := by rw [hlen.tmp_len_arr]; omega
    let l0 := s.tmp[0]'htm_gt0; let l1 := s.tmp[1]'htm_gt1
    have htmp_take2 : (s.tmp.take 2).map BitVec.toNat = [l0.toNat, l1.toNat] := by
      refine List.ext_getElem (by simp [hlen.tmp_len_arr]; omega) fun k hk _ => ?_
      match k, hk with | 0, _ => simp [l0] | 1, _ => simp [l1]
    rw [htmp_take2] at hlits_lt hent2
    have hl0_lt : l0.toNat < 2 * c.mv := hlits_lt _ (by simp)
    have hl1_lt : l1.toNat < 2 * c.mv := hlits_lt _ (by simp)
    have hent2_swap := entails_bin_swap hent2
    let b0 := (l1 &&& 0x7FFFFFFF#32) ||| 0x80000000#32
    let b1 := (l0 &&& 0x7FFFFFFF#32) ||| 0x80000000#32
    have hb0_ne : b0 ≠ 0xFFFFFFFF#32 := bv32_tag_bin_ne_sent (by omega)
    have hb1_ne : b1 ≠ 0xFFFFFFFF#32 := bv32_tag_bin_ne_sent (by omega)
    pi_steps; c0_call hPush
    refine ⟨c, s, R, rfl, hlen, hcore.watches.layout, (fun _ => hb0_ne),
      (fun hc => absurd hc (by decide)), hm, ?_⟩
    intro ok1 wvec1 wstk1 wlen1 wu1 wsort1 m1 s1 hlen1 hlay1 hoth1 hok1t hok1f hm1
    have htm1_gt1 : 1 < s1.tmp.length := by rw [hlen1.tmp_len_arr]; omega
    have hw1 := plainWatchPush_preserves_watchesInv hcore.watches hlay1 (fun _ hr => hr)
      (fun _ => ⟨bv32_tag_bin_flag l1, by rw [bv32_tag_bin_mask (by omega)]; exact hl1_lt,
        by rw [bv32_tag_bin_mask (by omega)]; exact hent2⟩)
      (fun hc => absurd hc (by decide)) hoth1 hok1t (fun h => (hok1f h).1)
    have hcore1 : PlainCoreInv c F0 s1 := { hcore with
      lengths := hlen1, arena := { hcore.arena with len_ok := hcore.arena.len_ok }, watches := hw1 }
    pi_steps
    · subst hc; c0_call hPush
      refine ⟨c, s1, R, rfl, hlen1, hlay1, (fun _ => hb1_ne),
        (fun hc => absurd hc (by decide)), hm1, ?_⟩
      intro ok2 wvec2 wstk2 wlen2 wu2 wsort2 m2 s2 hlen2 hlay2 hoth2 hok2t hok2f hm2
      have hw2 := plainWatchPush_preserves_watchesInv hw1 hlay2 (fun _ hr => hr)
        (fun _ => ⟨bv32_tag_bin_flag l0, by rw [bv32_tag_bin_mask (by omega)]; exact hl0_lt,
          by rw [bv32_tag_bin_mask (by omega)]; exact hent2_swap⟩)
        (fun hc => absurd hc (by decide)) hoth2 hok2t (fun h => (hok2f h).1)
      have hcore2 : PlainCoreInv c F0 s2 := { hcore1 with
        lengths := hlen2, arena := { hcore1.arena with len_ok := hcore1.arena.len_ok },
        watches := hw2 }
      pi_steps
      · have hcore_fin : PlainCoreInv c F0 { s2 with num_binary := s.num_binary + 1#64 } :=
          { hcore2 with
            lengths := { hcore2.lengths with vals_len := hcore2.lengths.vals_len }
            arena := { hcore2.arena with len_ok := hcore2.arena.len_ok }
            watches := hcore2.watches.with_wstk rfl rfl rfl rfl }
        exact hQ 0xFFFFFFFE#64 wvec2 wstk2 wlen2 wu2 (s.num_binary + 1#64) wsort2 _
          (Or.inr rfl) hcore_fin ‹_›
      · exact hQ 0xFFFFFFFF#64 wvec2 wstk2 wlen2 wu2 s.num_binary wsort2 m2 (Or.inl rfl) hcore2 hm2
    · exact hQ 0xFFFFFFFF#64 wvec1 wstk1 wlen1 wu1 s.num_binary wsort1 m1 (Or.inl rfl) hcore1 hm1
  · pi_head_steps
    refine wp_head_jnz_iff (b := decide (len.toNat < 3))
      (by simp only [Arg.val_var]; simpa [bv_ofNat_toNat_eq len] using
        bv32_ult_eq len.isLt (b := 3) (by decide)) ?_
    rw [decide_eq_true_eq, decide_eq_false_iff_not]; refine ⟨fun hlt3 => ?_, fun hge3 => ?_⟩
    · simp only [show len.toNat < 2 by omega, ↓reduceIte] at hQ; pi_steps; exact hQ
    · have hge3' : 3 ≤ len.toNat := by omega
      simp only [show ¬ (len.toNat < 2) by omega, hne2, ↓reduceIte] at hQ
      have hs_alen_lt32 : s.arena_len < 0xFFFFFFFF := by have := hlen.arena_len_le; omega
      have hcref_ne : BitVec.ofNat 64 s.arena_len ≠ 0xFFFFFFFF#64 := fun he => by
        have h := congrArg BitVec.toNat he
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h
        change s.arena_len = 0xFFFFFFFF at h; omega
      obtain ⟨hlits_lt, hent_cl⟩ := hcl_bd (by omega)
      pi_steps; c0_call hAlloc; refine ⟨c, s, R, rfl, hlen, hm, ?_⟩
      split
      · pi_steps
        · exact hQ 0xFFFFFFFF#64 s.arena s.arena_len s.wvec s.wstk s.wlen s.wusable
            s.first_reducible s.num_irred s.num_redundant s.heur.wsort m (Or.inl rfl)
            (fun _ => ⟨hcore, hm⟩) (fun hc => absurd hc.symm hcref_ne)
        · exact absurd rfl (by assumption)
      · intro arena1 m1 alen1 s1_st hlen1 hhold1 hnoshrk1 hnogarb1 _hred1 hsz1 hm1
        pi_steps
        refine wp_loop_group (ts := [i32]) (fun r (iv, ()) mc => ∃ i arena', i ≤ len.toNat ∧
            r = len.toNat - i ∧ iv = BitVec.ofNat 32 i ∧ arena'.length = c.arena_cap ∧
            (∀ k < s.arena_len + 3, arena'[k]? = arena1[k]?) ∧
            (∀ k < i, arena'[s.arena_len + 3 + k]? = s.tmp[k]?) ∧
            (PlainMem c { s1_st with arena := arena' } ⋆ R) mc) ?_ ?_
        · rintro L r ⟨iv, ⟨⟩⟩ mc ih ⟨i, arena', hile, rfl, rfl, harl, hpre, hcp, hmc⟩
          pi_head_steps
          refine wp_head_jnz_iff (b := decide (i < len.toNat)) (by
            simp only [Arg.val_var]
            simpa [bv_ofNat_toNat_eq len] using bv32_ult_eq (a := i) (by omega) len.isLt) ?_
          rw [decide_eq_true_eq, decide_eq_false_iff_not]; refine ⟨fun hilt => ?_, fun hige => ?_⟩
          · have htm_bd_i : i < { s1_st with arena := arena' }.tmp.length := by
              simp [s1_st, hlen.tmp_len_arr]; omega
            have har_bd : s.arena_len + 3 + i < arena'.length := by
              have := hlen1.arena_len_le; simp [s1_st, alen1] at this; omega
            have hidx_eq : ((BitVec.ofNat 32 i).setWidth 64) * 4 =
                BitVec.ofNat 64 (4 * i) := by
              rw [bv32_zext64_eq, bv32_ofNat_toNat (by omega)]; bv_omega
            have hidx2 : c.pArena + ((BitVec.ofNat 64 s.arena_len + (3 : BitVec 64) +
                BitVec.ofNat 64 i) * 4) =
                c.pArena + BitVec.ofNat 64 (4 * (s.arena_len + 3 + i)) := by bv_omega
            p_lets; try rw [hidx_eq]
            refine wp_load_of (load_arena_tmp (i := i) htm_bd_i hmc) ?_; p_lets
            rw [bv32_zext64_eq, bv32_ofNat_toNat (by omega), hidx2]
            let lit_i := s.tmp[i]'(by rw [hlen.tmp_len_arr]; omega)
            obtain ⟨ok_ar, hm_ar⟩ := store_arena_arena (i := s.arena_len + 3 + i) lit_i
              (by simpa [s1_st] using har_bd) hmc
            refine ⟨ok_ar, ?_⟩; p_lets
            rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
              show BitVec.ofNat 32 i + BitVec.ofNat 32 1 = BitVec.ofNat 32 (i + 1) by bv_omega]
            exact ih (len.toNat - (i + 1)) (BitVec.ofNat 32 (i + 1), ()) _ (by omega)
              ⟨i + 1, arena'.set (s.arena_len + 3 + i) lit_i, by omega, rfl, rfl, by simp [harl],
                (fun k hk => by rw [List.getElem?_set_ne (by omega)]; exact hpre k hk),
                (fun k hk => by
                  by_cases hki : k = i
                  · subst hki; rw [List.getElem?_set_self har_bd,
                      List.getElem?_eq_getElem (by rw [hlen.tmp_len_arr]; omega)]
                  · rw [List.getElem?_set_ne (by omega)]; exact hcp k (by omega)), hm_ar⟩
          · have hieq : i = len.toNat := by omega
            subst hieq; let s_cp : PlainState := { s1_st with arena := arena' }
            have hhold_cp : ∀ k < s.arena_len, arena'[k]? = s.arena[k]? := fun k hk =>
              (hpre k (by omega)).trans (hhold1 k hk)
            have hnoshrk_cp : (arena'[s.arena_len]?.getD 0#32 &&& 0x00800000#32) = 0#32 := by
              rw [hpre s.arena_len (by omega)]; exact hnoshrk1
            have hnogarb_cp : (arena'[s.arena_len]?.getD 0#32 &&& 0x00080000#32) = 0#32 := by
              rw [hpre s.arena_len (by omega)]; exact hnogarb1
            have hsz_cp : (arena'[s.arena_len + 2]?.getD 0#32).toNat = len.toNat := by
              rw [hpre (s.arena_len + 2) (by omega)]; exact hsz1
            have hrefs_cp : arenaClauseRefs s_cp = arenaClauseRefs s ++ [s.arena_len] :=
              arenaClauseRefs_append hcore.arena hge3' rfl hhold_cp hnoshrk_cp hsz_cp
            have hw_cp : WatchesInv c F0 s_cp :=
              plainWstackDefrag_preserves_watchesInv hcore.watches
                (hcore.watches.layout.with_wstk rfl rfl rfl)
                (fun r hr => hrefs_cp ▸ List.mem_append_left _ hr)
                fun _ _ => ⟨rfl, fun _ _ => rfl⟩
            have hlen_cp : s_cp.LengthsOk c :=
              { hlen1 with arena_len_arr := by simp [s_cp, harl] }
            have hlits_cp : arenaClauseLits s_cp s.arena_len =
                (s.tmp.take len.toNat).map BitVec.toNat := by
              have hle_len : s.arena_len + 3 + len.toNat ≤ arena'.length := by
                have := hlen1.arena_len_le; simp [s1_st, alen1] at this; omega
              apply List.ext_getElem
              · simp [arenaClauseLits, arenaClauseSize, s_cp, hsz_cp, harl,
                  hlen.tmp_len_arr]
                omega
              · intro k hk1 _
                have hk_lt : k < len.toNat := by
                  simp [arenaClauseLits, arenaClauseSize, s_cp, hsz_cp] at hk1; omega
                have hcpk := hcp k hk_lt
                rw [List.getElem?_eq_getElem (by omega),
                  List.getElem?_eq_getElem (by rw [hlen.tmp_len_arr]; omega)] at hcpk
                simp [arenaClauseLits, arenaClauseSize, s_cp, hsz_cp, Option.some.inj hcpk]
            have hcref32_ne : BitVec.ofNat 32 s.arena_len ≠ 0xFFFFFFFF#32 := fun he => by
              have ht := congrArg BitVec.toNat he
              rw [bv32_ofNat_toNat (by omega)] at ht; change s.arena_len = 0xFFFFFFFF at ht; omega
            have hcref32_lt : (BitVec.ofNat 32 s.arena_len).toNat < 0x80000000 := by
              rw [bv32_ofNat_toNat (by omega)]; omega
            refine wp_join_group (ts := []) (fun () mf => ∃ wvec' wstk' wlen' wusable' wsort',
              let sf : PlainState := { s_cp with
                wvec := wvec', wstk := wstk', wlen := wlen',
                wusable := wusable', heur := { s_cp.heur with wsort := wsort' } }
              sf.LengthsOk c ∧ WatchesInv c F0 sf ∧ (PlainMem c sf ⋆ R) mf) ?_ ?_
            · rintro _ ⟨⟩ mf ⟨wvec', wstk', wlen', wusable', wsort', hlen_w, hw_w, hmf⟩
              let s_w : PlainState := { s_cp with
                wvec := wvec', wstk := wstk', wlen := wlen',
                wusable := wusable', heur := { s_cp.heur with wsort := wsort' } }
              have har_bd0 : s.arena_len < s_w.arena.length := by
                have := hlen_w.arena_len_le; have h2 := hlen_w.arena_len_arr
                change s_w.arena.length = c.arena_cap at h2; omega
              p_lets
              have haddr_ar : c.pArena + BitVec.ofNat 64 s.arena_len * 4 =
                  c.pArena + BitVec.ofNat 64 (4 * s.arena_len) := by
                rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat,
                  bv64_ofNat_toNat (by omega)]
              rw [haddr_ar]
              refine wp_load_of (load_arena_arena (i := s.arena_len) har_bd0 hmf) ?_
              p_lets
              let hdr_g := arena'[s.arena_len]'(by omega) ||| 0x00080000#32
              let arena_g := arena'.set s.arena_len hdr_g
              let s_g : PlainState := { s_w with arena := arena_g }
              obtain ⟨ok_g, hm_g⟩ := store_arena_arena (i := s.arena_len) hdr_g
                (by simpa [s_w] using har_bd0) hmf
              refine ⟨ok_g, ?_⟩; p_lets
              have hhold_g : ∀ k < s.arena_len, arena_g[k]? = s.arena[k]? := fun k hk => by
                rw [List.getElem?_set_ne (by omega)]; exact hhold_cp k hk
              have hnoshrk_g : (arena_g[s.arena_len]?.getD 0#32 &&& 0x00800000#32) = 0#32 := by
                rw [List.getElem?_set_self (by omega), Option.getD_some]
                exact bv32_or_garb_noshrk (by
                  rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at hnoshrk_cp)
              have hnogarb_g : (arena_g[s.arena_len]?.getD 0#32 &&& 0x00080000#32) ≠ 0#32 := by
                rw [List.getElem?_set_self (by omega), Option.getD_some]; exact bv32_or_garb_nz _
              have hsz_g : (arena_g[s.arena_len + 2]?.getD 0#32).toNat = len.toNat := by
                rw [List.getElem?_set_ne (by omega)]; exact hsz_cp
              have hlen_g : s_g.LengthsOk c :=
                { hlen_w with arena_len_arr := by simp [s_g, arena_g, harl] }
              have hrefs_g : arenaClauseRefs s_g = arenaClauseRefs s ++ [s.arena_len] :=
                arenaClauseRefs_append hcore.arena hge3' rfl hhold_g hnoshrk_g hsz_g
              have hw_g : WatchesInv c F0 s_g := plainWstackDefrag_preserves_watchesInv hw_w
                (hw_w.layout.with_wstk rfl rfl rfl) (fun r hr => by
                  have h1 : arenaClauseRefs s_w = arenaClauseRefs s ++ [s.arena_len] := hrefs_cp
                  rwa [hrefs_g, ← h1]) fun _ _ => ⟨rfl, fun _ _ => rfl⟩
              have hcore_g := addGarbageClause_preserves_core (s := s) (arena' := arena_g)
                (wvec' := wvec') (wstk' := wstk') (wlen' := wlen') (wusable' := wusable')
                (wsort' := wsort') hcore hge3' hhold_g hnoshrk_g hnogarb_g hsz_g hlen_g hw_g
              exact hQ 0xFFFFFFFF#64 arena_g alen1 wvec' wstk' wlen' wusable' s.first_reducible
                s.num_irred s.num_redundant wsort' _ (Or.inl rfl) (fun _ => ⟨hcore_g, hm_g⟩)
                (fun hc => absurd hc.symm hcref_ne)
            · intro Jw hJw
              have htm_cp0 : 0 < s_cp.tmp.length := by simp [s_cp, s1_st, hlen.tmp_len_arr]; omega
              have htm_cp1 : 1 < s_cp.tmp.length := by simp [s_cp, s1_st, hlen.tmp_len_arr]; omega
              pi_steps; rw [bv64_trunc32_ofNat (by omega)]; c0_call hPush
              refine ⟨c, s_cp, R, rfl, hlen_cp, hw_cp.layout, (fun hc => absurd hc (by decide)),
                (fun _ => ⟨bv32_mask_ne_sent _, hcref32_ne⟩), hmc, ?_⟩
              intro ok1 wvec1 wstk1 wlen1 wu1 wsort1 m1 s1 hlen1 hlay1 hoth1 hok1t hok1f hm1
              have htm_s1_0 : 0 < s1.tmp.length := by
                simp [s1, s_cp, s1_st, hlen1.tmp_len_arr]; omega
              have htm_s1_1 : 1 < s1.tmp.length := by
                simp [s1, s_cp, s1_st, hlen1.tmp_len_arr]; omega
              have hrefs1 : arenaClauseRefs s1 = arenaClauseRefs s_cp := rfl
              have hw1 := plainWatchPush_preserves_watchesInv hw_cp hlay1
                (fun r hr => hrefs1 ▸ hr)
                (fun hc => absurd hc (by decide)) (fun _ => ⟨bv32_mask_flag0 _, hcref32_lt,
                  hrefs1 ▸ hrefs_cp ▸ List.mem_append_right _
                    (by simp [bv32_ofNat_toNat (by omega : s.arena_len < 2 ^ 32)])⟩)
                hoth1 hok1t (fun h => (hok1f h).1)
              pi_steps
              · rw [bv64_trunc32_ofNat (by omega)]; c0_call hPush
                refine ⟨c, s1, R, rfl, hlen1, hlay1, (fun hc => absurd hc (by decide)),
                  (fun _ => ⟨bv32_mask_ne_sent _, hcref32_ne⟩), hm1, ?_⟩
                intro ok2 wvec2 wstk2 wlen2 wu2 wsort2 m2 s2 hlen2 hlay2 hoth2 hok2t hok2f hm2
                have hrefs2 : arenaClauseRefs s2 = arenaClauseRefs s1 := rfl
                have hw2 := plainWatchPush_preserves_watchesInv hw1 hlay2
                  (fun r hr => hrefs2 ▸ hr)
                  (fun hc => absurd hc (by decide)) (fun _ => ⟨bv32_mask_flag0 _, hcref32_lt,
                    hrefs2 ▸ hrefs1 ▸ hrefs_cp ▸ List.mem_append_right _
                      (by simp [bv32_ofNat_toNat (by omega : s.arena_len < 2 ^ 32)])⟩)
                  hoth2 hok2t (fun h => (hok2f h).1)
                have hfin : ∀ fred' ni' nr' mf,
                    (PlainMem c (addClauseState s len.toNat arena' wvec2 wstk2 wlen2 wu2
                      fred' ni' nr' wsort2) ⋆ R) mf → Q (BitVec.ofNat 64 s.arena_len, ()) mf :=
                  fun fred' ni' nr' mf hm_f => by
                    let s_fin := addClauseState s len.toNat arena' wvec2 wstk2 wlen2 wu2
                      fred' ni' nr' wsort2
                    have hlen_f : s_fin.LengthsOk c :=
                      { hlen2 with arena_len_arr := by simp [s_fin, addClauseState, harl] }
                    have hrefs_f : arenaClauseRefs s_fin = arenaClauseRefs s ++ [s.arena_len] :=
                      arenaClauseRefs_append hcore.arena hge3' rfl hhold_cp hnoshrk_cp hsz_cp
                    have hw_f : WatchesInv c F0 s_fin :=
                      plainWstackDefrag_preserves_watchesInv hw2
                      (hw2.layout.with_wstk rfl rfl rfl) (fun r hr => by
                        have h1 : arenaClauseRefs s2 = arenaClauseRefs s ++ [s.arena_len] :=
                          hrefs2.trans (hrefs1.trans hrefs_cp)
                        rwa [hrefs_f, ← h1]) fun _ _ => ⟨rfl, fun _ _ => rfl⟩
                    have hcore_f := addClause_preserves_core hcore hlen_f hge3' hlits_lt hent_cl
                      hhold_cp hnoshrk_cp hnogarb_cp hsz_cp hlits_cp hw_f
                    have hgarb_f : arenaClauseGarb s_fin s.arena_len = false := by
                      unfold arenaClauseGarb arenaHdr s_fin addClauseState; simp [hnogarb_cp]
                    exact hQ (BitVec.ofNat 64 s.arena_len) arena' alen1 wvec2 wstk2 wlen2 wu2
                      fred' ni' nr' wsort2 mf (Or.inr rfl) (fun hc => absurd hc hcref_ne)
                      (fun _ => ⟨rfl, hcore_f, hrefs_f ▸ List.mem_append_right _ (by simp),
                        hgarb_f, hlits_cp, hm_f⟩)
                pi_steps
                · exact hfin (BitVec.ofNat 64 s.arena_len) s.num_irred (s.num_redundant + 1#64)
                    _ (by assumption)
                · exact hfin s.first_reducible s.num_irred (s.num_redundant + 1#64) _
                    (by assumption)
                · exact hfin s.first_reducible (s.num_irred + 1#64) s.num_redundant _
                    (by assumption)
                · exact hJw () m2 ⟨wvec2, wstk2, wlen2, wu2, wsort2, hlen2, hw2, hm2⟩
              · exact hJw () m1 ⟨wvec1, wstk1, wlen1, wu1, wsort1, hlen1, hw1, hm1⟩
        · intro L hL; pi_steps; exact hL len.toNat _ m1 ⟨0, arena1, Nat.zero_le _, by simp, rfl,
            hlen1.arena_len_arr, fun _ _ => rfl, fun _ h => by omega, hm1⟩

/-! ## 2. `plain_skip_cl` & `plain_ingest_cl` -/

private theorem plainIngest_unit_rev {revLits : List Nat} {l : Nat}
    (hcleq : CNF.Clause.ofLiterals (revLits.reverse.map kissatLitToDimacsLiteral) =
      CNF.Clause.ofLiterals [kissatLitToDimacsLiteral l]) : revLits = [l] := by
  have hlits_eq := congrArg CNF.Clause.literals hcleq
  simp only [CNF.Clause.literals_ofLiterals] at hlits_eq
  cases hr : revLits.reverse with
  | nil => rw [hr] at hlits_eq; simp at hlits_eq
  | cons a rest_r =>
    rw [hr] at hlits_eq
    cases rest_r with
    | nil =>
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hlits_eq
      have ha := kissatLitToDimacsLiteral_inj hlits_eq; subst ha
      simpa using congrArg List.reverse hr
    | cons _ _ => simp at hlits_eq

private def IngestReadInv (c : PlainCfg) (cnfBytes : List UInt8) (i0 idx tlen : Nat)
    (taut : Bool) (revLits : List Nat) (st : PlainState) : Prop :=
  i0 ≤ idx ∧ idx ≤ cnfBytes.length ∧ tlen ≤ c.mv ∧ st.mrk.length = c.mv ∧ st.tmp.length = c.mv ∧
  (∀ k < tlen, (st.tmp[k]?.getD 0#32).toNat < 2 * c.mv) ∧
  (∀ k1 k2, k1 < tlen → k2 < tlen →
    (st.tmp[k1]?.getD 0#32).toNat / 2 = (st.tmp[k2]?.getD 0#32).toNat / 2 → k1 = k2) ∧
  (∀ v < c.mv, (∀ k < tlen, (st.tmp[k]?.getD 0#32).toNat / 2 ≠ v) → st.mrk[v]?.getD 0#8 = 0#8) ∧
  (∀ k < tlen, st.mrk[(st.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#8 =
    BitVec.ofNat 8 ((st.tmp[k]?.getD 0#32).toNat % 2 + 1)) ∧
  (taut = false → ∀ l ∈ revLits, ∃ k < tlen, (st.tmp[k]?.getD 0#32).toNat = l) ∧
  (∀ k < tlen, (st.tmp[k]?.getD 0#32).toNat ∈ revLits) ∧ (revLits = [] → taut = false) ∧
  (∀ l, revLits = [l] → taut = false ∧ tlen = 1 ∧ (st.tmp[0]?.getD 0#32).toNat = l)

private theorem ingestReadInv_push {c : PlainCfg} {cnfBytes : List UInt8}
    {i0 idx j tlen l : Nat} {taut : Bool} {revLits : List Nat} {s : PlainState}
    {mrk' : List (BitVec 8)} {tmp' : List (BitVec 32)} {cnf_ptr dcur_n dv_n : BitVec 64}
    (hi_j : i0 ≤ j) (hj : j ≤ cnfBytes.length) (htl : tlen < c.mv) (hmkl : mrk'.length = c.mv)
    (htmpl : tmp'.length = c.mv) (hl_mv : l < 2 * c.mv) (hl32 : l < 2 ^ 32) (hv_lt : l / 2 < c.mv)
    (hmiss_v : ∀ k < tlen, (tmp'[k]?.getD 0#32).toNat / 2 ≠ l / 2)
    (hri : IngestReadInv c cnfBytes i0 idx tlen taut revLits
      { s with d_cur := cnf_ptr + BitVec.ofNat 64 idx, mrk := mrk', tmp := tmp' }) :
    IngestReadInv c cnfBytes i0 j (tlen + 1) taut (l :: revLits)
      { s with
        d_cur := dcur_n, d_val := dv_n,
        mrk := mrk'.set (l / 2) (BitVec.ofNat 8 (l % 2 + 1)),
        tmp := tmp'.set tlen (BitVec.ofNat 32 l) } := by
  rcases hri with ⟨_, _, _, _, _, htmp_lt, htmp_nd, hmrk_zero, hmrk_pos, hcov, hsub_rev,
    hnil_taut, _⟩
  have hn_lt : tlen < tmp'.length := by rw [htmpl]; exact htl
  have hm_lt : l / 2 < mrk'.length := by rw [hmkl]; exact hv_lt
  refine ⟨hi_j, hj, by omega, by simp [hmkl], by simp [htmpl], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk; by_cases hkt : k = tlen
    · subst k; simp [List.getElem?_set_self hn_lt, bv32_ofNat_toNat hl32, hl_mv]
    · simp [List.getElem?_set_ne (Ne.symm hkt), htmp_lt k (by omega)]
  · intro k1 k2 h1 h2 heq; by_cases hk1 : k1 = tlen <;> by_cases hk2 : k2 = tlen
    · omega
    · subst hk1; simp [List.getElem?_set_self hn_lt, List.getElem?_set_ne (Ne.symm hk2),
        bv32_ofNat_toNat hl32] at heq; exact absurd heq.symm (hmiss_v k2 (by omega))
    · subst hk2; simp [List.getElem?_set_self hn_lt, List.getElem?_set_ne (Ne.symm hk1),
        bv32_ofNat_toNat hl32] at heq; exact absurd heq (hmiss_v k1 (by omega))
    · simp [List.getElem?_set_ne (Ne.symm hk1), List.getElem?_set_ne (Ne.symm hk2)] at heq
      exact htmp_nd k1 k2 (by omega) (by omega) heq
  · intro v hv hmiss
    have hne : v ≠ l / 2 := by
      have h := hmiss tlen (by omega)
      simp [List.getElem?_set_self hn_lt, bv32_ofNat_toNat hl32] at h; exact Ne.symm h
    rw [List.getElem?_set_ne (Ne.symm hne)]
    exact hmrk_zero v hv fun k hk => by
      have h := hmiss k (by omega); simpa [List.getElem?_set_ne (by omega : tlen ≠ k)] using h
  · intro k hk; by_cases hkt : k = tlen
    · subst k; simp [List.getElem?_set_self hn_lt, List.getElem?_set_self hm_lt,
        bv32_ofNat_toNat hl32]
    · simp [List.getElem?_set_ne (Ne.symm hkt),
        List.getElem?_set_ne (Ne.symm (hmiss_v k (by omega))), hmrk_pos k (by omega)]
  · intro ht x hx; rcases List.mem_cons.mp hx with rfl | hx'
    · exact ⟨tlen, by omega, by simp [List.getElem?_set_self hn_lt, bv32_ofNat_toNat hl32]⟩
    · obtain ⟨k, hk, hget⟩ := hcov ht x hx'
      exact ⟨k, by omega, by simpa [List.getElem?_set_ne (by omega : tlen ≠ k)] using hget⟩
  · intro k hk; by_cases hkt : k = tlen
    · subst k; simp [List.getElem?_set_self hn_lt, bv32_ofNat_toNat hl32]
    · simp only [List.getElem?_set_ne (Ne.symm hkt)]
      exact List.mem_cons_of_mem l (hsub_rev k (by omega))
  · intro hc; cases hc
  · intro l' hl'; rcases List.cons.inj hl' with ⟨rfl, rfl⟩
    have ht0 : tlen = 0 := by
      cases tlen with | zero => rfl | succ k => exact absurd (hsub_rev 0 (by omega)) (by simp)
    subst ht0
    exact ⟨hnil_taut rfl, rfl, by simp [List.getElem?_set_self hn_lt, bv32_ofNat_toNat hl32]⟩

private def IngestPruneInv (c : PlainCfg) (s : PlainState) (tmp' : List (BitVec 32))
    (revLits : List Nat) (tlen keep i : Nat) (tmp'' : List (BitVec 32)) : Prop :=
  keep ≤ i ∧ i ≤ tlen ∧ tmp''.length = c.mv ∧
  (∀ k, i ≤ k → k < tlen → tmp''[k]? = tmp'[k]?) ∧
  (∀ k < keep, (tmp''[k]?.getD 0#32).toNat < 2 * c.mv ∧
    s.vals[(tmp''[k]?.getD 0#32).toNat]?.getD 0#8 = 0#8) ∧
  (∀ k < i, (∃ j < keep, tmp''[j]? = tmp'[k]?) ∨
    s.vals[(tmp'[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8) ∧
  (∀ l < 2 * c.mv, revLits = [l] → s.vals[l]?.getD 0#8 = 0#8 →
    i = 1 → keep = 1 ∧ (tmp''[0]?.getD 0#32).toNat = l) ∧
  (∀ l < 2 * c.mv, revLits = [l] → s.vals[l]?.getD 0#8 = 0xFF#8 → i = 1 → keep = 0)

private theorem ingestPruneInv_push {c : PlainCfg} {s : PlainState} {tmp' tmp'' : List (BitVec 32)}
    {revLits : List Nat} {tlen keep i : Nat} {li : BitVec 32}
    (hlt : i < tlen) (htlen_le : tlen ≤ c.mv) (htmpl : tmp'.length = c.mv)
    (hli_eq : li = tmp'[i]'(by rw [htmpl]; omega)) (hli_lt : li.toNat < 2 * c.mv)
    (hlv_getD : s.vals[li.toNat]?.getD 0#8 = 0#8)
    (hunit0 : ∀ l, revLits = [l] → (tmp'[0]?.getD 0#32).toNat = l)
    (hpi : IngestPruneInv c s tmp' revLits tlen keep i tmp'') :
    IngestPruneInv c s tmp' revLits tlen (keep + 1) (i + 1) (tmp''.set keep li) := by
  rcases hpi with ⟨hk_le, hi_le, htmp'l, htail, hkeep_un, hpruned, _, _⟩
  refine ⟨by omega, by omega, by simp [htmp'l], ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk1 hk2; rw [List.getElem?_set_ne (by omega)]; exact htail k (by omega) hk2
  · intro k hk; by_cases hkk : k = keep
    · subst k; rw [List.getElem?_set_self (by rw [htmp'l]; omega), Option.getD_some]
      exact ⟨hli_lt, hlv_getD⟩
    · rw [List.getElem?_set_ne (Ne.symm hkk)]; exact hkeep_un k (by omega)
  · intro k hk; by_cases hki : k = i
    · subst k; refine Or.inl ⟨keep, by omega, ?_⟩
      rw [List.getElem?_set_self (by rw [htmp'l]; omega),
        List.getElem?_eq_getElem (by rw [htmpl]; omega), hli_eq]
    · rcases hpruned k (by omega) with ⟨j, hj, hjeq⟩ | hfl
      · exact Or.inl ⟨j, by omega, by rw [List.getElem?_set_ne (by omega)]; exact hjeq⟩
      · exact Or.inr hfl
  · intro l _ hrev _ hi1
    have hi0 : i = 0 := by omega
    have hk0 : keep = 0 := by omega
    subst hi0 hk0; refine ⟨rfl, ?_⟩
    rw [List.getElem?_set_self (by rw [htmp'l]; omega), Option.getD_some, hli_eq]
    simpa [List.getElem?_eq_getElem (l := tmp') (i := 0) (by rw [htmpl]; omega)] using hunit0 l hrev
  · intro l _ hrev hvf hi1
    have hi0 : i = 0 := by omega
    subst hi0; have hl0 := hunit0 l hrev
    rw [List.getElem?_eq_getElem (l := tmp') (i := 0) (by rw [htmpl]; omega), Option.getD_some,
      ← hli_eq] at hl0
    rw [← hl0] at hvf; exact absurd (hlv_getD.symm.trans hvf) (by decide)

private theorem ingestPruneInv_skip {c : PlainCfg} {s : PlainState} {tmp' tmp'' : List (BitVec 32)}
    {revLits : List Nat} {tlen keep i : Nat} {li : BitVec 32}
    (hlt : i < tlen) (htlen_le : tlen ≤ c.mv) (htmpl : tmp'.length = c.mv)
    (hli_eq : li = tmp'[i]'(by rw [htmpl]; omega)) (hlv_ff : s.vals[li.toNat]?.getD 0#8 = 0xFF#8)
    (hunit0 : ∀ l, revLits = [l] → (tmp'[0]?.getD 0#32).toNat = l)
    (hpi : IngestPruneInv c s tmp' revLits tlen keep i tmp'') :
    IngestPruneInv c s tmp' revLits tlen keep (i + 1) tmp'' := by
  rcases hpi with ⟨hk_le, hi_le, htmp'l, htail, hkeep_un, hpruned, _, _⟩
  refine ⟨by omega, by omega, htmp'l, fun k hk1 hk2 => htail k (by omega) hk2, hkeep_un, ?_, ?_, ?_⟩
  · intro k hk; by_cases hki : k = i
    · subst k; refine Or.inr ?_
      rw [List.getElem?_eq_getElem (i := i) (by rw [htmpl]; omega), Option.getD_some, ← hli_eq]
      exact hlv_ff
    · exact hpruned k (by omega)
  · intro l _ hrev hv0 hi1
    have hi0 : i = 0 := by omega
    subst hi0; have hl0 := hunit0 l hrev
    rw [List.getElem?_eq_getElem (l := tmp') (i := 0) (by rw [htmpl]; omega), Option.getD_some,
      ← hli_eq] at hl0
    rw [← hl0] at hv0; exact absurd (hlv_ff.symm.trans hv0) (by decide)
  · intro _ _ _ _ _; omega

private theorem ingest_keep_entails {c : PlainCfg} {accCnf : CNF Nat} {cl : CNF.Clause Nat}
    {s : PlainState} {tmp' tmp'' : List (BitVec 32)} {revLits : List Nat} {tlen keep : Nat}
    (hcore : PlainCoreInv c (shiftDownCnf accCnf) s) (hcl0 : s.cur_level = 0)
    (htlen_le : tlen ≤ c.mv) (htmpl : tmp'.length = c.mv)
    (htmp_lt : ∀ k < tlen, (tmp'[k]?.getD 0#32).toNat < 2 * c.mv)
    (hF1_cl : (shiftDownCnf (accCnf.add cl)).EntailsClause
      (cnfClause ((tmp'.take tlen).map BitVec.toNat)))
    (hpi : IngestPruneInv c s tmp' revLits tlen keep tlen tmp'') :
    (shiftDownCnf (accCnf.add cl)).EntailsClause
      (cnfClause ((tmp''.take keep).map BitVec.toNat)) := by
  rcases hpi with ⟨hk_le, _, htmp'l, _, _, hpruned, _, _⟩
  refine entails_of_mem_or_false hF1_cl fun l hl => ?_
  rw [List.mem_map] at hl; obtain ⟨x, hx, rfl⟩ := hl
  rw [List.mem_iff_getElem] at hx; obtain ⟨k, hk, hxk⟩ := hx
  have hklt : k < tlen := by rw [List.length_take] at hk; omega
  rw [List.getElem_take] at hxk
  rcases hpruned k hklt with ⟨j, hj, hjeq⟩ | hfl
  · refine Or.inl (List.mem_map.mpr ⟨x, ?_, rfl⟩)
    rw [List.mem_iff_getElem]; refine ⟨j, by rw [List.length_take]; omega, ?_⟩
    rw [List.getElem_take]; rw [List.getElem?_eq_getElem (by rw [htmp'l]; omega),
      List.getElem?_eq_getElem (by rw [htmpl]; omega)] at hjeq
    exact (Option.some.inj hjeq).trans hxk
  · refine Or.inr ?_
    have hxk_get : (tmp'[k]?.getD 0#32).toNat = x.toNat := by
      rw [List.getElem?_eq_getElem (by rw [htmpl]; omega), Option.getD_some, hxk]
    rw [hxk_get] at hfl
    have hx_lt : x.toNat < 2 * c.mv := by have := htmp_lt k hklt; rwa [hxk_get] at this
    obtain ⟨ti, hti, htr_eq⟩ := (hcore.vals_false_iff x.toNat hx_lt).mp hfl
    have hlvl0 : (s.lvl[(s.trl[ti]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
      have := hcore.lvl_le ti hti; omega
    have hent0 := hcore.level0_sound ti hti hlvl0
    have hent_F1 : (shiftDownCnf (accCnf.add cl)).EntailsClause
        (cnfClause [(s.trl[ti]?.getD 0#32).toNat]) :=
      CNF.entails_clause_trans (shiftDownCnf_entails_add accCnf cl) hent0
    rwa [htr_eq] at hent_F1

private abbrev IngestPost (c : PlainCfg) (accCnf : CNF Nat) (s : PlainState)
    (cnf_ptr : BitVec 64) (cnfBytes : List UInt8) (i0 : Nat) (R : Mem 64 → Prop)
    (Q : Post [i64]) (cl : CNF.Clause Nat) (rest : List UInt8) : Prop :=
  ∀ r s' j m', (∀ lit ∈ cl.literals, 1 ≤ lit.1) → i0 < j → j ≤ cnfBytes.length →
    cnfBytes.drop j = rest → s'.LengthsOk c → s'.d_cur = cnf_ptr + BitVec.ofNat 64 j →
    s'.cur_level = 0 → s'.fuel = s.fuel → s'.oom = s.oom → s'.probing = s.probing →
    s'.heur.rel_trigger = s.heur.rel_trigger → (r = 1#64 ∨ r = 2#64 ∨ r = 3#64) →
    (r = 1#64 → PlainInv c (shiftDownCnf (accCnf.add cl)) s') →
    (r = 2#64 → (shiftDownCnf (accCnf.add cl)).Unsat) →
    (∀ l < 2 * c.mv, cl = CNF.Clause.ofLiterals [kissatLitToDimacsLiteral l] →
      s.vals[l]?.getD 0#8 = 0#8 →
      r = 1#64 ∧ s'.vals = (s.vals.set l 1#8).set (l ^^^ 1) 0xFF#8 ∧
      s'.trail_end = s.trail_end + 1 ∧ s'.propagated = s.propagated ∧
      s'.arena_len = s.arena_len ∧ s'.wlen = s.wlen ∧ s'.wvec = s.wvec) →
    (∀ l < 2 * c.mv, cl = CNF.Clause.ofLiterals [kissatLitToDimacsLiteral l] →
      s.vals[l]?.getD 0#8 = 0xFF#8 → r = 2#64) →
    (bytes cnf_ptr cnfBytes ⋆ PlainMem c s' ⋆ R) m' → Q (r, ()) m'

private theorem ingest_st3_inv {c : PlainCfg} {F1 : CNF Nat} {st2 st3 : PlainState}
    (hinv : PlainInv c F1 st2) (hlen3 : st3.LengthsOk c) (hmrk : st3.mrk = st2.mrk)
    (hs1 : st3 = { st2 with tmp := st3.tmp }) : PlainInv c F1 st3 := by
  have hm : MarksClear c st3 := fun v hv => by rw [hmrk]; exact hinv.marks v hv
  rw [hs1] at hlen3 ⊢
  exact ⟨{ hinv.core with
    lengths := hlen3, arena := { hinv.core.arena with len_ok := hinv.core.arena.len_ok }
    watches := hinv.core.watches.with_wstk rfl rfl rfl rfl }, by simpa [← hs1] using hm⟩

private theorem ingest_ret_exit {c : PlainCfg} {accCnf : CNF Nat} {s st_out : PlainState}
    {cnf_ptr : BitVec 64} {cnfBytes : List UInt8} {i0 idx : Nat} {revLits : List Nat}
    {r_out : BitVec 64} {R : Mem 64 → Prop} {m_out : Mem 64} {Q : Post [i64]}
    (hcl_pos : ∀ lit ∈ (CNF.Clause.ofLiterals
      (revLits.reverse.map kissatLitToDimacsLiteral)).literals, 1 ≤ lit.1)
    (hi0 : i0 < idx) (hidx : idx ≤ cnfBytes.length) (hlens : st_out.LengthsOk c)
    (hd : st_out.d_cur = cnf_ptr + BitVec.ofNat 64 idx) (hcl : st_out.cur_level = 0)
    (hfu : st_out.fuel = s.fuel) (hoom : st_out.oom = s.oom) (hpr : st_out.probing = s.probing)
    (hrt : st_out.heur.rel_trigger = s.heur.rel_trigger)
    (hdom : r_out = 1#64 ∨ r_out = 2#64 ∨ r_out = 3#64)
    (hi1 : r_out = 1#64 → PlainInv c (shiftDownCnf (accCnf.add
      (CNF.Clause.ofLiterals (revLits.reverse.map kissatLitToDimacsLiteral)))) st_out)
    (hi2 : r_out = 2#64 → (shiftDownCnf (accCnf.add
      (CNF.Clause.ofLiterals (revLits.reverse.map kissatLitToDimacsLiteral)))).Unsat)
    (hno_u0 : ∀ l < 2 * c.mv, revLits = [l] → s.vals[l]?.getD 0#8 = 0#8 →
      r_out = 1#64 ∧ st_out.vals = (s.vals.set l 1#8).set (l ^^^ 1) 0xFF#8 ∧
      st_out.trail_end = s.trail_end + 1 ∧ st_out.propagated = s.propagated ∧
      st_out.arena_len = s.arena_len ∧ st_out.wlen = s.wlen ∧ st_out.wvec = s.wvec)
    (hno_u1 : ∀ l < 2 * c.mv, revLits = [l] → s.vals[l]?.getD 0#8 = 0xFF#8 → r_out = 2#64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ PlainMem c st_out ⋆ R) m_out)
    (hQ : IngestPost c accCnf s cnf_ptr cnfBytes i0 R Q
      (CNF.Clause.ofLiterals (revLits.reverse.map kissatLitToDimacsLiteral))
      (cnfBytes.drop idx)) : Q (r_out, ()) m_out :=
  hQ r_out st_out idx m_out hcl_pos hi0 hidx rfl hlens hd hcl hfu hoom hpr hrt hdom hi1 hi2
    (fun l hl hcleq => hno_u0 l hl (plainIngest_unit_rev hcleq))
    (fun l hl hcleq => hno_u1 l hl (plainIngest_unit_rev hcleq)) hm

private theorem ingest_dup_cov {mv tlen : Nat} {tmp' : List (BitVec 32)} {mrk' : List (BitVec 8)}
    {revLits : List Nat} {taut' taut_v : Bool} {l k0 : Nat} {mv_b : BitVec 8}
    (hmkl : mrk'.length = mv) (hv_lt : l / 2 < mv) (hk0 : k0 < tlen)
    (htaut' : taut' = if mv_b = BitVec.ofNat 8 (l % 2 + 1) then taut_v else true)
    (hmv_b : mv_b = mrk'[l / 2]'(by omega))
    (hmv_pos : mrk'[l / 2]'(by omega) = BitVec.ofNat 8 ((tmp'[k0]?.getD 0#32).toNat % 2 + 1))
    (hcov : taut_v = false → ∀ x ∈ revLits, ∃ k < tlen, (tmp'[k]?.getD 0#32).toNat = x)
    (hk0_v : (tmp'[k0]?.getD 0#32).toNat / 2 = l / 2) :
    taut' = false → ∀ x ∈ l :: revLits, ∃ k < tlen, (tmp'[k]?.getD 0#32).toNat = x := by
  intro hnt' x hx
  by_cases hmeq : mv_b = BitVec.ofNat 8 (l % 2 + 1)
  · simp only [hmeq, ↓reduceIte] at htaut'
    rcases List.mem_cons.mp hx with rfl | hx'
    · refine ⟨k0, hk0, ?_⟩
      have h1 := hmv_pos.symm.trans (hmv_b.symm.trans hmeq)
      have hmod := congrArg BitVec.toNat h1
      simp only [BitVec.toNat_ofNat] at hmod; omega
    · exact hcov (htaut' ▸ hnt') x hx'
  · simp only [hmeq, ↓reduceIte] at htaut'; rw [htaut'] at hnt'; cases hnt'

theorem plain_skip_cl_wp (Γ : Env)
    (hLit : ∀ args m Q X, kissatNextLitSpec args m Q X →
      Γ "kissat_next_lit" [i64, i64] [i64] args m Q X) :
    ∀ args m Q X, plainSkipClSpec args m Q X → Func.wp Γ plain_skip_cl_body args m Q X := by
  rintro ⟨cend, d, ⟨⟩⟩ m Q X ⟨cnf_ptr, nc, val0, mv, cnfBytes, i0, R, rfl, hfit, hmv64, hi0, hm, hQ⟩
  unfold Func.wp plain_skip_cl_body; wp_unfold
  refine wp_loop_group
    (fun r () ml => ∃ idx val_l revLits,
      i0 ≤ idx ∧ idx ≤ cnfBytes.length ∧ r = cnfBytes.length - idx ∧
      (∀ lit ∈ revLits, 1 ≤ lit.1) ∧
      parseClauseAux ((cnfBytes.drop idx).length + 1) mv revLits (cnfBytes.drop idx) =
        parseClause mv (cnfBytes.drop i0) ∧
      (bytes cnf_ptr cnfBytes ⋆
        dimacsState d (BitVec.ofNat 64 mv) nc (cnf_ptr + BitVec.ofNat 64 idx) val_l ⋆ R) ml)
    ?_ ?_
  · rintro L r ⟨⟩ ml ih ⟨idx, val_l, revLits, hi_le, hidx, rfl, hpos_acc, hpc_inv, hml⟩
    pi_steps
    · c0_call hLit
      refine ⟨cnf_ptr, nc, val_l, mv, cnfBytes, idx, R, rfl, hfit, hmv64, hidx, hml, ?_⟩
      cases hnl : nextLitPure mv (cnfBytes.drop idx) with
      | err =>
        intro cur' val' m' hm'; pi_steps
        · rw [← hpc_inv, parseClauseAux_eq_nextLitPure, hnl] at hQ; exact hQ cur' val' m' hm'
        · exact absurd rfl (by assumption : ¬(0#64 : BitVec 64) = 0)
      | endClause rest =>
        intro j m' hij hj hdrop hm'; pi_steps
        · rw [← hpc_inv, parseClauseAux_eq_nextLitPure, hnl] at hQ
          refine hQ j m' (fun lit hlit => ?_) (by omega) hj hdrop hm'
          simp only [CNF.Clause.literals_ofLiterals, List.mem_reverse] at hlit
          exact hpos_acc lit hlit
        · exact absurd rfl (by assumption : ¬(1#64 : BitVec 64) = 1)
      | lit l rest =>
        intro j m' _ _ hij hj hdrop hm'; pi_steps
        refine ih (cnfBytes.length - j) () m' (by omega)
          ⟨j, BitVec.ofNat 64 l, kissatLitToDimacsLiteral l :: revLits, by omega, hj, rfl,
            fun lit hlit => (List.mem_cons.mp hlit).elim
              (fun h => h ▸ by simp [kissatLitToDimacsLiteral]) (hpos_acc lit), ?_, hm'⟩
        have hstep :
            parseClauseAux ((cnfBytes.drop idx).length + 1) mv revLits (cnfBytes.drop idx) =
            parseClauseAux (cnfBytes.drop idx).length mv (kissatLitToDimacsLiteral l :: revLits)
              (cnfBytes.drop j) := by rw [parseClauseAux_eq_nextLitPure, hnl, ← hdrop]
        rw [← hpc_inv, hstep]; exact parseClauseAux_fuel_irrel (by simp) (by simp; omega)
    · cases (by assumption : true = false)
  · intro L hL; pi_steps; exact hL (cnfBytes.length - i0) () m
      ⟨i0, val0, [], Nat.le_refl _, hi0, rfl, (fun _ h => by cases h), rfl, hm⟩

theorem plain_ingest_cl_wp (Γ : Env)
    (hLit : ∀ args m Q X, kissatNextLitSpec args m Q X →
      Γ "kissat_next_lit" [i64, i64] [i64] args m Q X)
    (hAssign : ∀ args m Q X, plainAssignSpec args m Q X →
      Γ "plain_assign" [i64, i32, i32] [] args m Q X)
    (hAddCl : ∀ args m Q X, plainAddClauseSpec args m Q X →
      Γ "plain_add_clause" [i64, i32, i32, .bool] [i64] args m Q X) :
    ∀ args m Q X, plainIngestClSpec args m Q X → Func.wp Γ plain_ingest_cl_body args m Q X := by
  rintro ⟨h, cend, ⟨⟩⟩ m Q X
    ⟨c, accCnf, s, cnf_ptr, cnfBytes, i0, R, rfl, rfl, hfit, hi0, hdcur, hcl0, hinv, hm, hQ⟩
  have hmv := c.hmv; unfold dimacsBound at hmv; have hcore := hinv.core; have hlen := hcore.lengths
  unfold Func.wp plain_ingest_cl_body; p_lets
  have hm0 : (PlainMem c s ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m := sep_ac hm
  refine wp_load_of (load_arena_tmp_lits hm0) ?_; p_lets
  refine wp_load_of (load_arena_mark hm0) ?_; p_lets
  refine wp_load_of (load_arena_values hm0) ?_; p_lets
  let st_r (dc dv : BitVec 64) (mk : List (BitVec 8)) (tp : List (BitVec 32)) : PlainState :=
    { s with d_cur := dc, d_val := dv, mrk := mk, tmp := tp }
  have hst0 : st_r (cnf_ptr + BitVec.ofNat 64 i0) s.d_val s.mrk s.tmp = s := by rw [← hdcur]
  refine wp_loop_break_group (brkTs := [i32, .bool, .bool]) (lpTs := [i32, .bool])
    (fun (tlen_v, taut_v, err_v, ()) mb => ∃ idx tlen revLits mrk' tmp' dcur dval,
      let st := st_r dcur dval mrk' tmp'
      tlen_v = BitVec.ofNat 32 tlen ∧ IngestReadInv c cnfBytes i0 idx tlen taut_v revLits st ∧
      (err_v = true → parseClause c.mv (cnfBytes.drop i0) = none) ∧
      (err_v = false → i0 < idx ∧ dcur = cnf_ptr + BitVec.ofNat 64 idx ∧
        parseClause c.mv (cnfBytes.drop i0) =
          some (CNF.Clause.ofLiterals (revLits.reverse.map kissatLitToDimacsLiteral),
            cnfBytes.drop idx)) ∧
      (bytes cnf_ptr cnfBytes ⋆ PlainMem c st ⋆ R) mb)
    (fun r (tlen_v, taut_v, ()) ml => ∃ idx tlen revLits mrk' tmp' dval,
      let st := st_r (cnf_ptr + BitVec.ofNat 64 idx) dval mrk' tmp'
      r = cnfBytes.length - idx ∧ tlen_v = BitVec.ofNat 32 tlen ∧
      IngestReadInv c cnfBytes i0 idx tlen taut_v revLits st ∧
      parseClauseAux ((cnfBytes.drop idx).length + 1) c.mv
        (revLits.map kissatLitToDimacsLiteral) (cnfBytes.drop idx) =
        parseClause c.mv (cnfBytes.drop i0) ∧
      (bytes cnf_ptr cnfBytes ⋆ PlainMem c st ⋆ R) ml)
    ?_ ?_ ?_
  · rintro _ ⟨tlen_v, taut_v, err_v, ⟨⟩⟩ mb
      ⟨idx, tlen, revLits, mrk', tmp', dcur, dval, rfl, hri, herr_p, hok_p, hmb⟩
    obtain ⟨hi_le, hidx, htlen_le, hmkl, htmpl, htmp_lt, htmp_nd,
      hmrk_zero, hmrk_pos, hcov, hsub_rev, hnil_taut, hunit_r⟩ := hri
    p_lets
    refine wp_loop_group (ts := [i32])
      (fun r2 (kv, ()) m2 => ∃ k mrk'',
        k ≤ tlen ∧ r2 = tlen - k ∧ kv = BitVec.ofNat 32 k ∧ mrk''.length = c.mv ∧
        (∀ v < c.mv, (∀ j, k ≤ j → j < tlen → (tmp'[j]?.getD 0#32).toNat / 2 ≠ v) →
          mrk''[v]?.getD 0#8 = 0#8) ∧
        (bytes cnf_ptr cnfBytes ⋆ PlainMem c (st_r dcur dval mrk'' tmp') ⋆ R) m2) ?_ ?_
    · rintro L2 r2 ⟨kv, ⟨⟩⟩ m2 ih2 ⟨k, mrk'', hkle, rfl, rfl, hmk''l, hclr, hm2⟩
      p_lets
      have hult_k := bv32_ult_eq (a := k) (b := tlen) (by omega) (by omega)
      refine wp_head_jnz_iff (b := decide (k < tlen)) (by simpa [Arg.val_var] using hult_k) ?_
      rw [decide_eq_true_eq, decide_eq_false_iff_not]
      refine ⟨fun hklt => ?_, fun hkge => ?_⟩
      · p_lets
        have hm2a : (PlainMem c (st_r dcur dval mrk'' tmp') ⋆
            (bytes cnf_ptr cnfBytes ⋆ R)) m2 := sep_ac hm2
        rw [bv32_zext64_eq, bv32_ofNat_toNat (by omega), bv64_mul4_nat]
        have htm_bd_k : k < (st_r dcur dval mrk'' tmp').tmp.length := by
          dsimp [st_r]; rw [htmpl]; omega
        refine wp_load_of (load_arena_tmp (i := k) htm_bd_k hm2a) ?_; p_lets
        let kv32 := tmp'[k]'(by rw [htmpl]; omega)
        have hkv32_st : (st_r dcur dval mrk'' tmp').tmp[k]'htm_bd_k = kv32 := rfl
        rw [hkv32_st]
        have hkvar_lt : kv32.toNat / 2 < c.mv := by
          have := htmp_lt k hklt
          dsimp only [st_r] at this
          rw [List.getElem?_eq_getElem (by rw [htmpl]; omega), Option.getD_some] at this
          change kv32.toNat < 2 * c.mv at this; omega
        refine wp_join_group (ts := [])
          (fun () m_in => ∃ mrk''', mrk'''.length = c.mv ∧
            (∀ v < c.mv, (∀ j, k + 1 ≤ j → j < tlen → (tmp'[j]?.getD 0#32).toNat / 2 ≠ v) →
              mrk'''[v]?.getD 0#8 = 0#8) ∧
            (bytes cnf_ptr cnfBytes ⋆ PlainMem c (st_r dcur dval mrk''' tmp') ⋆ R) m_in)
          (fun _ ⟨⟩ m_in ⟨mrk''', hmk'''l, hclr''', hm_in⟩ => by
            p_lets; rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
              show BitVec.ofNat 32 k + BitVec.ofNat 32 1 = BitVec.ofNat 32 (k + 1) by bv_omega]
            exact ih2 (tlen - (k + 1)) _ m_in (by omega)
              ⟨k + 1, mrk''', by omega, rfl, rfl, hmk'''l, hclr''', hm_in⟩)
          (fun Jk hJk => by
            p_lets; refine wp_load_of (load_arena_mv hm2a) ?_; p_lets
            rw [bv32_zext64_eq, bv32_lshr1]
            have hult_kv : (BitVec.ofNat 64 (kv32.toNat / 2)).ult (BitVec.ofNat 64 c.mv) =
                true := by rw [bv_ult_eq (by omega) (by omega)]; simp [hkvar_lt]
            refine wp_head_jnz_iff (b := true) (by simpa [Arg.val_var] using hult_kv) ?_
            refine ⟨fun _ => ?_, fun h => (by cases h)⟩
            p_lets; rw [bv32_zext64_eq, bv32_lshr1]
            have hmk_bd_kv : kv32.toNat / 2 < (st_r dcur dval mrk'' tmp').mrk.length := by
              dsimp [st_r]; rw [hmk''l]; exact hkvar_lt
            obtain ⟨okm, hmm⟩ := store_arena_mrk (i := kv32.toNat / 2) 0#8 hmk_bd_kv hm2a
            refine ⟨okm, ?_⟩; p_lets
            have heq : ({ st_r dcur dval mrk'' tmp' with
                mrk := mrk''.set (kv32.toNat / 2) 0#8 } : PlainState) =
                st_r dcur dval (mrk''.set (kv32.toNat / 2) 0#8) tmp' := rfl
            rw [heq] at hmm
            refine hJk () _ ⟨mrk''.set (kv32.toNat / 2) 0#8, by simp [hmk''l],
              fun v hv hmiss => by
                by_cases hveq : v = kv32.toNat / 2
                · subst v; rw [List.getElem?_set_self (by rw [hmk''l]; exact hkvar_lt)]; rfl
                · rw [List.getElem?_set_ne (Ne.symm hveq)]
                  exact hclr v hv fun j hj1 hj2 => if hj_eq : j = k then by
                    subst j
                    rw [List.getElem?_eq_getElem (l := tmp') (by rw [htmpl]; omega),
                      Option.getD_some]
                    exact Ne.symm hveq
                  else hmiss j (by omega) hj2, sep_ac hmm⟩)
      · have hkeq : k = tlen := by omega
        subst k
        let st2 := st_r dcur dval mrk'' tmp'
        have hlen2 : st2.LengthsOk c := { hlen with mrk_len := hmk''l, tmp_len_arr := htmpl }
        have hmrk_clr : MarksClear c st2 := fun v hv => hclr v hv (fun j hj1 hj2 => by omega)
        have hcore2 : PlainCoreInv c (shiftDownCnf accCnf) st2 :=
          { hcore with
            lengths := hlen2, arena := { hcore.arena with len_ok := hcore.arena.len_ok }
            watches := hcore.watches.with_wstk rfl rfl rfl rfl }
        have hinv2 : PlainInv c (shiftDownCnf accCnf) st2 := ⟨hcore2, hmrk_clr⟩
        p_lets; refine wp_head_jnz_iff (b := err_v) (by c0_val_eq) ?_
        refine ⟨fun herr => ?_, fun hnoerr => ?_⟩
        · have hnone := herr_p herr; rw [hnone] at hQ; p_lets
          exact hQ st2 m2 hlen2 rfl rfl rfl rfl hm2
        · obtain ⟨hi0_lt, hdcur_eq, hpc_some⟩ := hok_p hnoerr
          subst hdcur_eq
          let cl := CNF.Clause.ofLiterals (revLits.reverse.map kissatLitToDimacsLiteral)
          have hcl_pos : ∀ lit ∈ cl.literals, 1 ≤ lit.1 := by
            intro lit hlit; simp only [cl, CNF.Clause.literals_ofLiterals, List.mem_map] at hlit
            rcases hlit with ⟨l, _, rfl⟩; simp [kissatLitToDimacsLiteral]
          rw [hpc_some] at hQ
          let F1 := shiftDownCnf (accCnf.add cl)
          have hinv2_F1 : PlainInv c F1 st2 :=
            PlainInv.mono (shiftDownCnf_entails_add accCnf cl) hinv2
          refine wp_head_jnz_iff (b := taut_v) (by c0_val_eq) ?_
          refine ⟨fun htaut => ?_, fun hntaut => ?_⟩
          · p_lets
            exact ingest_ret_exit hcl_pos hi0_lt hidx hlen2 rfl hcl0 rfl rfl rfl rfl (Or.inl rfl)
              (fun _ => hinv2_F1) (fun h => by cases h)
              (fun l _ hr _ => by have := (hunit_r l hr).1; rw [htaut] at this; cases this)
              (fun l _ hr _ => by have := (hunit_r l hr).1; rw [htaut] at this; cases this)
              hm2 hQ
          · have hF1_cl : F1.EntailsClause (cnfClause ((tmp'.take tlen).map BitVec.toNat)) := by
              have hcl_ent : F1.EntailsClause (cnfClause revLits.reverse) := by
                have h1 := shiftDownCnf_entails_added accCnf cl
                rwa [show shiftDownClause cl = cnfClause revLits.reverse from
                  shiftDownClause_kissatLits revLits.reverse] at h1
              refine entails_of_mem_or_false hcl_ent fun l hl => Or.inl ?_
              obtain ⟨k, hk, hget⟩ := hcov hntaut l (List.mem_reverse.mp hl)
              rw [List.mem_map]; refine ⟨tmp'[k]'(by rw [htmpl]; omega), ?_, ?_⟩
              · rw [List.mem_iff_getElem]
                exact ⟨k, by rw [List.length_take, htmpl]; omega, by rw [List.getElem_take]⟩
              · dsimp only [st_r] at hget
                rwa [List.getElem?_eq_getElem (by rw [htmpl]; omega), Option.getD_some] at hget
            p_lets
            refine wp_loop_group (ts := [i32, i32])
              (fun r3 (kp_v, iv, ()) m3 => ∃ keep i tmp'',
                r3 = tlen - i ∧ kp_v = BitVec.ofNat 32 keep ∧ iv = BitVec.ofNat 32 i ∧
                IngestPruneInv c s tmp' revLits tlen keep i tmp'' ∧
                (bytes cnf_ptr cnfBytes ⋆
                  PlainMem c (st_r (cnf_ptr + BitVec.ofNat 64 idx) dval mrk'' tmp'') ⋆ R) m3) ?_ ?_
            · rintro L3 r3 ⟨kp_v, iv, ⟨⟩⟩ m3 ih3 ⟨keep, i, tmp'', rfl, rfl, rfl, hpi, hm3⟩
              have ⟨hk_le, hi_le3, htmp'l, htail, hkeep_un, _, hu0, hu1⟩ := hpi
              p_lets
              refine wp_head_jnz_iff (b := decide (i < tlen))
                (by simp only [Arg.val_var]; exact bv32_ult_eq (by omega) (by omega)) ?_
              rw [decide_eq_true_eq, decide_eq_false_iff_not]; refine ⟨fun hilt => ?_,
                  fun hige => ?_⟩
              · p_lets
                have hm3a : (PlainMem c (st_r (cnf_ptr + BitVec.ofNat 64 idx) dval mrk'' tmp'') ⋆
                    (bytes cnf_ptr cnfBytes ⋆ R)) m3 := sep_ac hm3
                rw [bv32_zext64_eq, bv32_ofNat_toNat (by omega), bv64_mul4_nat]
                have htm_bd_i : i < (st_r (cnf_ptr + BitVec.ofNat 64 idx)
                    dval mrk'' tmp'').tmp.length := by dsimp [st_r]; rw [htmp'l]; omega
                refine wp_load_of (load_arena_tmp (i := i) htm_bd_i hm3a) ?_; p_lets
                let li := tmp''[i]'(by rw [htmp'l]; omega)
                have hli_st : (st_r (cnf_ptr + BitVec.ofNat 64 idx)
                    dval mrk'' tmp'').tmp[i]'htm_bd_i = li := rfl
                rw [hli_st]
                have hli_eq : li = tmp'[i]'(by rw [htmpl]; omega) := by
                  have h1 := htail i (Nat.le_refl _) hilt
                  rw [List.getElem?_eq_getElem (by rw [htmp'l]; omega),
                    List.getElem?_eq_getElem (by rw [htmpl]; omega)] at h1; exact Option.some.inj h1
                have hli_lt : li.toNat < 2 * c.mv := by
                  have := htmp_lt i hilt; dsimp only [st_r] at this
                  rwa [List.getElem?_eq_getElem (by rw [htmpl]; omega),
                    Option.getD_some, ← hli_eq] at this
                rw [bv32_zext64_eq]
                have hv_bd_li : li.toNat < (st_r (cnf_ptr + BitVec.ofNat 64 idx)
                    dval mrk'' tmp'').vals.length := by
                  dsimp [st_r]; rw [hlen.vals_len]; exact hli_lt
                refine wp_load_of (load_arena_vals hv_bd_li hm3a) ?_; p_lets
                let lv := s.vals[li.toNat]'(by rw [hlen.vals_len]; exact hli_lt)
                have hlv_eq : (st_r (cnf_ptr + BitVec.ofNat 64 idx)
                    dval mrk'' tmp'').vals[li.toNat]'hv_bd_li = lv := rfl
                have hlv_dom : lv = 0#8 ∨ lv = 1#8 ∨ lv = 0xFF#8 := by
                  have := hcore.vals_domain li.toNat hli_lt
                  rwa [List.getElem?_eq_getElem (by rw [hlen.vals_len]; exact hli_lt),
                    Option.getD_some] at this
                have hlv_getD : s.vals[li.toNat]?.getD 0#8 = lv := by
                  rw [List.getElem?_eq_getElem (l := s.vals) (by rw [hlen.vals_len]; exact hli_lt),
                    Option.getD_some]
                have hsgt : (0#32).slt (lv.signExtend 32) = true ↔ lv = 1#8 :=
                  i8_vals_sgt0 hlv_dom
                rw [wp_jnz]; dsimp only [Arg.val_var]; rw [hlv_eq]
                refine ⟨fun hpos => ?_, fun hnpos => ?_⟩
                · have hlv1 : lv = 1#8 := hsgt.mp hpos
                  let st3 := st_r (cnf_ptr + BitVec.ofNat 64 idx) dval mrk'' tmp''
                  have hlen3 : st3.LengthsOk c := { hlen2 with tmp_len_arr := htmp'l }
                  have hinv3 := ingest_st3_inv hinv2_F1 hlen3 rfl rfl
                  have hli_abs : ∀ l, revLits = [l] → s.vals[l]?.getD 0#8 = 1#8 := fun l hrev => by
                    obtain ⟨_, _, htmp0⟩ := hunit_r l hrev; dsimp only [st_r] at htmp0
                    have hi0_eq : i = 0 := by omega
                    subst hi0_eq
                    have hl_eq : li.toNat = l := by
                      rw [hli_eq]; rwa [List.getElem?_eq_getElem (by rw [htmpl]; omega),
                        Option.getD_some] at htmp0
                    rw [hl_eq] at hlv_getD; exact hlv_getD.trans hlv1
                  p_lets
                  exact ingest_ret_exit hcl_pos hi0_lt hidx hlen3 rfl hcl0 rfl rfl rfl rfl
                    (Or.inl rfl) (fun _ => hinv3) (fun h => by cases h)
                    (fun l _ hr hv0 => by have h1 := hli_abs l hr; rw [h1] at hv0; cases hv0)
                    (fun l _ hr hvf => by have h1 := hli_abs l hr; rw [h1] at hvf; cases hvf)
                    hm3 hQ
                · have hlv_ne1 : lv ≠ 1#8 := fun h => by rw [hsgt.mpr h] at hnpos; cases hnpos
                  refine wp_join_group
                    (fun (kp', ()) m3' => ∃ keep' tmp''', kp' = BitVec.ofNat 32 keep' ∧
                      IngestPruneInv c s tmp' revLits tlen keep' (i + 1) tmp''' ∧
                      (bytes cnf_ptr cnfBytes ⋆
                        PlainMem c (st_r (cnf_ptr + BitVec.ofNat 64 idx) dval mrk'' tmp''') ⋆ R)
                        m3')
                    (fun _ ⟨kp', ⟨⟩⟩ m3' ⟨keep', tmp''', hkp', hpi', hm3'⟩ => by
                      subst hkp'; p_lets
                      rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
                        show BitVec.ofNat 32 i + BitVec.ofNat 32 1 = BitVec.ofNat 32 (i + 1)
                          by bv_omega]
                      exact ih3 (tlen - (i + 1)) _ m3' (by omega)
                        ⟨keep', i + 1, tmp''', rfl, rfl, rfl, hpi', hm3'⟩)
                    (fun Jp hJp => by
                      p_lets; refine wp_head_jnz_iff (b := decide (lv = 0#8)) (by
                        simp only [Arg.val_var]; exact i8_vals_beq0 hlv_dom) ?_
                      rw [decide_eq_true_eq, decide_eq_false_iff_not]
                      refine ⟨fun hlv0 => ?_, fun hlvne0 => ?_⟩
                      · p_lets
                        rw [bv32_zext64_eq, bv32_ofNat_toNat (n := keep) (by omega), bv64_mul4_nat]
                        have htm_bd_kp : keep < (st_r (cnf_ptr + BitVec.ofNat 64 idx)
                            dval mrk'' tmp'').tmp.length := by dsimp [st_r]; rw [htmp'l]; omega
                        obtain ⟨okt, hmt⟩ := store_arena_tmp (i := keep) li htm_bd_kp hm3a
                        refine ⟨okt, ?_⟩; p_lets
                        rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
                          show BitVec.ofNat 32 keep + BitVec.ofNat 32 1 =
                            BitVec.ofNat 32 (keep + 1) by bv_omega]
                        exact hJp _ _ ⟨keep + 1, tmp''.set keep li, rfl,
                          ingestPruneInv_push hilt htlen_le htmpl hli_eq hli_lt
                            (hlv_getD.trans hlv0) (fun l hr => (hunit_r l hr).2.2) hpi,
                          sep_ac hmt⟩
                      · have hlv_ff : lv = 0xFF#8 := by
                          rcases hlv_dom with h | h | h
                          · exact absurd h hlvne0
                          · exact absurd h hlv_ne1
                          · exact h
                        exact hJp _ m3 ⟨keep, tmp'', rfl,
                          ingestPruneInv_skip hilt htlen_le htmpl hli_eq (hlv_getD.trans hlv_ff)
                            (fun l hr => (hunit_r l hr).2.2) hpi, hm3⟩)
              · have hieq : i = tlen := by omega
                subst i
                have hF1_keep := ingest_keep_entails hcore hcl0 htlen_le htmpl htmp_lt hF1_cl hpi
                let st3 := st_r (cnf_ptr + BitVec.ofNat 64 idx) dval mrk'' tmp''
                have hlen3 : st3.LengthsOk c := { hlen2 with tmp_len_arr := htmp'l }
                have hinv3 := ingest_st3_inv hinv2_F1 hlen3 rfl rfl
                p_lets
                have hkeep0 : (BitVec.ofNat 32 keep == 0#32) = decide (keep = 0) := by
                  rw [show (0#32 : BitVec 32) = BitVec.ofNat 32 0 from rfl,
                    bv32_beq_nat_eq (by decide), bv32_ofNat_toNat (n := keep) (by omega)]
                refine wp_head_jnz_iff (b := decide (keep = 0))
                  (by simpa [Arg.val_var] using hkeep0) ?_
                rw [decide_eq_true_eq, decide_eq_false_iff_not]; refine ⟨fun hk0 => ?_, fun _ => ?_⟩
                · subst hk0; p_lets
                  have hunsat : F1.Unsat := unsat_of_entails_nil (by simpa using hF1_keep)
                  exact ingest_ret_exit hcl_pos hi0_lt hidx hlen3 rfl hcl0 rfl rfl rfl rfl
                    (Or.inr (Or.inl rfl)) (fun h => by cases h) (fun _ => hunsat)
                    (fun l hl hr hv0 => by
                      have ⟨_, ht1, _⟩ := hunit_r l hr; have ⟨h1, _⟩ := hu0 l hl hr hv0 ht1; omega)
                    (fun _ _ _ _ => rfl) hm3 hQ
                · p_lets
                  have hkeep1 : (BitVec.ofNat 32 keep == 1#32) = decide (keep = 1) := by
                    rw [show (1#32 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
                      bv32_beq_nat_eq (by decide), bv32_ofNat_toNat (n := keep) (by omega)]
                  refine wp_head_jnz_iff (b := decide (keep = 1))
                    (by simpa [Arg.val_var] using hkeep1) ?_
                  rw [decide_eq_true_eq, decide_eq_false_iff_not]; refine ⟨fun hk1 => ?_,
                      fun _ => ?_⟩
                  · subst hk1; p_lets
                    have hm3a : (PlainMem c st3 ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m3 := sep_ac hm3
                    have htm_bd0 : 0 < st3.tmp.length := by dsimp [st3, st_r]; rw [htmp'l]; omega
                    refine wp_load_of (load_arena_tmp (i := 0) htm_bd0 hm3a) ?_; p_lets
                    let l0 := tmp''[0]'(by rw [htmp'l]; omega)
                    have hl0_st : st3.tmp[0]'htm_bd0 = l0 := rfl
                    rw [hl0_st]
                    have ⟨hl0_lt, hl0_un⟩ := hkeep_un 0 (by decide)
                    rw [List.getElem?_eq_getElem (i := 0) (by rw [htmp'l]; omega),
                      Option.getD_some] at hl0_lt hl0_un
                    have hl0_lt' : l0.toNat < 2 * c.mv := hl0_lt
                    have hl0_ent : F1.EntailsClause (cnfClause [l0.toNat]) := by
                      have htk : tmp''.take 1 = [l0] := by
                        cases tmp'' with | nil => simp at htmp'l; omega | cons _ _ => rfl
                      simpa [htk] using hF1_keep
                    apply wp_call_of_spec; apply hAssign
                    dsimp only [plainAssignSpec, vals_nil, vals_cons, Arg.val_var, Arg.val_imm]
                    refine ⟨c, st3, bytes cnf_ptr cnfBytes ⋆ R, rfl, hlen3,
                      by simp [st3, st_r, hcl0], hm3a, ?_⟩
                    have hte_lt := hinv3.core.trail_end_lt_of_unassigned hl0_lt' hl0_un
                    simp only [show ¬ (c.mv ≤ l0.toNat / 2 ∨ c.mv ≤ st3.trail_end) by omega,
                      ↓reduceIte]
                    intro phases' m4 hph hlen_sf hm4; p_lets
                    have hcl_st3 : st3.cur_level = 0 := hcl0
                    simp only [hcl_st3, ↓reduceIte] at hlen_sf hm4
                    let sf : PlainState :=
                      { st3 with
                        vals := (st3.vals.set l0.toNat 1#8).set (l0.toNat ^^^ 1) 0xFF#8,
                        lvl := st3.lvl.set (l0.toNat / 2) (BitVec.ofNat 32 st3.cur_level),
                        rsns := st3.rsns.set (l0.toNat / 2) 0xFFFFFFFF#32,
                        trl := st3.trl.set st3.trail_end l0,
                        trail_pos := st3.trail_pos.set (l0.toNat / 2)
                          (BitVec.ofNat 32 st3.trail_end),
                        trail_end := st3.trail_end + 1, unflushed := st3.unflushed + 1#64,
                        heur := { st3.heur with phases := phases' } }
                    have hsf_core : PlainCoreInv c F1 sf := by
                      simpa [sf, hcl_st3] using assign_preserves_core hinv3.core
                        (rsn := 0xFFFFFFFF#32) (unflushed' := st3.unflushed + 1#64) hl0_lt' hph
                        hl0_un (by simp [hcl_st3]) (fun L _ h2 => by omega)
                        (fun _ => hl0_ent) (fun hc => absurd hcl_st3 hc)
                    exact hQ 1#64 sf idx m4 hcl_pos hi0_lt hidx rfl hsf_core.lengths rfl hcl0 rfl
                      rfl rfl rfl (Or.inl rfl) (fun _ => ⟨hsf_core, hinv3.marks⟩)
                      (fun h => by cases h) (fun l hl hcleq hv0 => by
                        have hrev := plainIngest_unit_rev hcleq
                        have ⟨_, ht1, _⟩ := hunit_r l hrev
                        have ⟨_, hl0eq⟩ := hu0 l hl hrev hv0 ht1
                        rw [List.getElem?_eq_getElem (i := 0) (by rw [htmp'l]; omega),
                          Option.getD_some] at hl0eq
                        have hl0eq' : l0.toNat = l := hl0eq
                        exact ⟨rfl, by simp [sf, st3, st_r, hl0eq'], rfl, rfl, rfl, rfl, rfl⟩)
                      (fun l hl hcleq hvf => by
                        have hrev := plainIngest_unit_rev hcleq
                        have ⟨_, ht1, _⟩ := hunit_r l hrev
                        have := hu1 l hl hrev hvf ht1; omega)
                      (by
                        have hm4' : (PlainMem c sf ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m4 := by
                          simpa [sf, hcl_st3] using hm4
                        exact sep_ac hm4')
                  · have hkp_ge2 : 2 ≤ keep := by omega
                    have hm3a : (PlainMem c st3 ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m3 := sep_ac hm3
                    have hlits_take :
                        (∀ l ∈ (tmp''.take keep).map BitVec.toNat, l < 2 * c.mv) ∧
                        F1.EntailsClause (cnfClause ((tmp''.take keep).map BitVec.toNat)) := by
                      refine ⟨?_, hF1_keep⟩
                      intro l hl; rw [List.mem_map] at hl; obtain ⟨x, hx, rfl⟩ := hl
                      rw [List.mem_iff_getElem] at hx; obtain ⟨k, hk, hxk⟩ := hx
                      rw [List.length_take] at hk; rw [List.getElem_take] at hxk
                      have hlt := (hkeep_un k (by omega)).1
                      rwa [List.getElem?_eq_getElem (by rw [htmp'l]; omega),
                        Option.getD_some, hxk] at hlt
                    have hq_ret : ∀ (r_out : BitVec 64) (sf : PlainState) m4
                        (hdom : r_out = 1#64 ∨ r_out = 3#64) (hlens : sf.LengthsOk c)
                        (hd : sf.d_cur = cnf_ptr + BitVec.ofNat 64 idx) (hcl : sf.cur_level = 0)
                        (hfu : sf.fuel = s.fuel) (hoom : sf.oom = s.oom)
                        (hpr : sf.probing = s.probing)
                        (hrt : sf.heur.rel_trigger = s.heur.rel_trigger)
                        (hi1 : r_out = 1#64 → PlainInv c F1 sf)
                        (hm4 : (PlainMem c sf ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m4),
                        Q (r_out, ()) m4 :=
                      fun r_out sf m4 hdom hlens hd hcl hfu hoom hpr hrt hi1 hm4 =>
                        ingest_ret_exit hcl_pos hi0_lt hidx hlens hd hcl hfu hoom hpr hrt
                          (hdom.elim Or.inl (fun h => Or.inr (Or.inr h))) hi1
                          (fun h => by rcases hdom with rfl | rfl <;> cases h)
                          (fun l hl hr hv0 => by
                            have ⟨_, ht1, _⟩ := hunit_r l hr
                            have ⟨h1, _⟩ := hu0 l hl hr hv0 ht1; omega)
                          (fun l hl hr hvf => by
                            have ⟨_, ht1, _⟩ := hunit_r l hr; have := hu1 l hl hr hvf ht1; omega)
                          (sep_ac hm4) hQ
                    apply wp_call_of_spec; apply hAddCl
                    dsimp only [plainAddClauseSpec, vals_nil, vals_cons, Arg.val_var, Arg.val_imm]
                    refine ⟨c, F1, st3, bytes cnf_ptr cnfBytes ⋆ R, rfl, hinv3.core,
                      by rw [bv32_ofNat_toNat (n := keep) (by omega)]; omega,
                      (fun _ => by
                        rw [bv32_ofNat_toNat (n := keep) (by omega)]; exact hlits_take),
                      hm3a, ?_⟩
                    simp only [bv32_ofNat_toNat (n := keep) (by omega),
                      show ¬ (keep < 2) by omega, ↓reduceIte]
                    by_cases hkp2 : keep = 2
                    · simp only [hkp2, ↓reduceIte]
                      intro cid wvec' wstk' wlen' wu' nb' wsort' m4 hr_dom hcore4 hm4
                      let sf : PlainState := { st3 with
                        wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu',
                        num_binary := nb', heur := { st3.heur with wsort := wsort' } }
                      have hinv4 : PlainInv c F1 sf :=
                        ⟨hcore4, fun v hv => by simpa [sf, st3, st_r] using hinv3.marks v hv⟩
                      p_lets; refine wp_head_jnz_iff (b := decide (cid = 0xFFFFFFFF#64))
                        (by simp only [Arg.val_var]; exact bv64_beq_eq) ?_
                      rw [decide_eq_true_eq, decide_eq_false_iff_not]; refine ⟨fun _ => ?_,
                          fun _ => ?_⟩
                      · p_lets; exact hq_ret 3#64 sf m4 (Or.inr rfl) hcore4.lengths rfl hcl0
                          rfl rfl rfl rfl (fun h => by cases h) hm4
                      · p_lets; exact hq_ret 1#64 sf m4 (Or.inl rfl) hcore4.lengths rfl hcl0
                          rfl rfl rfl rfl (fun _ => hinv4) hm4
                    · simp only [hkp2, ↓reduceIte]
                      intro cid arena' alen' wvec' wstk' wlen' wu' fred' ni' nr' wsort' m4
                        hr_dom hfail hok
                      p_lets; refine wp_head_jnz_iff (b := decide (cid = 0xFFFFFFFF#64))
                        (by simp only [Arg.val_var]; exact bv64_beq_eq) ?_
                      rw [decide_eq_true_eq, decide_eq_false_iff_not]
                      refine ⟨fun hoom_cid => ?_, fun hok_cid => ?_⟩
                      · obtain ⟨hcore4, hm4⟩ := hfail hoom_cid
                        let sf : PlainState := { st3 with
                          arena := arena', arena_len := alen', wvec := wvec', wstk := wstk',
                          wlen := wlen', wusable := wu', heur := { st3.heur with wsort := wsort' } }
                        p_lets; exact hq_ret 3#64 sf m4 (Or.inr rfl) hcore4.lengths rfl hcl0
                          rfl rfl rfl rfl (fun h => by cases h) hm4
                      · have hcid_eq : cid = BitVec.ofNat 64 st3.arena_len := by
                          rcases hr_dom with hc | hc <;> first | exact absurd hc hok_cid | exact hc
                        obtain ⟨_, hcore4, _, _, _, hm4⟩ := hok hcid_eq
                        let sf := addClauseState st3 keep arena' wvec' wstk' wlen' wu' fred'
                          ni' nr' wsort'
                        have hinv4 : PlainInv c F1 sf := ⟨hcore4, fun v hv => by
                          simpa [sf, addClauseState, st3, st_r] using hinv3.marks v hv⟩
                        p_lets; exact hq_ret 1#64 sf m4 (Or.inl rfl) hcore4.lengths rfl hcl0
                          rfl rfl rfl rfl (fun _ => hinv4) hm4
            · intro L3 hL3; p_lets
              exact hL3 tlen _ m2
                ⟨0, 0, tmp', by simp, rfl, rfl,
                  ⟨Nat.le_refl _, Nat.zero_le _, htmpl, fun _ _ _ => rfl,
                    fun _ h => by omega, fun _ h => by omega,
                    fun _ _ _ _ h => by omega, fun _ _ _ _ h => by omega⟩, hm2⟩
    · intro L2 hL2; p_lets
      exact hL2 tlen _ mb
        ⟨0, mrk', Nat.zero_le _, by simp, rfl, hmkl,
          fun v hv hmiss => hmrk_zero v hv (fun j hj => hmiss j (Nat.zero_le _) hj), hmb⟩
  · rintro B1 L1 r ⟨tlen_v, taut_v, ⟨⟩⟩ ml hB1 ih1
      ⟨idx, tlen, revLits, mrk', tmp', dval, rfl, rfl, hri, hpc_inv, hml⟩
    let st := st_r (cnf_ptr + BitVec.ofNat 64 idx) dval mrk' tmp'
    obtain ⟨hi_le, hidx, htlen_le, hmkl, htmpl, htmp_lt, htmp_nd,
      hmrk_zero, hmrk_pos, hcov, hsub_rev, hnil_taut, hunit_r⟩ := hri
    p_lets
    refine wp_head_jnz_iff (b := true) (by c0_val_eq) ?_
    refine ⟨fun _ => ?_, fun h => (by cases h)⟩
    p_lets
    have hml_d : (bytes cnf_ptr cnfBytes ⋆
        dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
          (cnf_ptr + BitVec.ofNat 64 idx) dval ⋆ (PlainRest c st ⋆ R)) ml := by
      have h1 := hml; rw [plainMem_eq_dimacs_sep] at h1; exact sep_ac h1
    apply wp_call_of_spec; apply hLit
    change kissatNextLitSpec (cnf_ptr + BitVec.ofNat 64 cnfBytes.length, c.hdr, ()) ml _ _
    refine ⟨cnf_ptr, BitVec.ofNat 64 c.nc, dval, c.mv, cnfBytes, idx, PlainRest c st ⋆ R,
      rfl, hfit, by omega, hidx, hml_d, ?_⟩
    cases hnl : nextLitPure c.mv (cnfBytes.drop idx) with
    | err =>
      intro cur' val' m' hm'; p_lets; refine wp_head_jnz_iff (by c0_val_eq) ?_
      refine ⟨fun _ => ?_, fun h => (by cases h)⟩
      let st_d := { st with d_cur := cur', d_val := val' }
      have hm'_a : (bytes cnf_ptr cnfBytes ⋆ PlainMem c st_d ⋆ R) m' := by
        rw [plainMem_eq_dimacs_sep, plainRest_d_irrel]; exact sep_ac hm'
      p_lets
      exact hB1 (BitVec.ofNat 32 tlen, taut_v, true, ()) m'
        ⟨idx, tlen, revLits, mrk', tmp', cur', val', rfl,
          ⟨hi_le, hidx, htlen_le, hmkl, htmpl, htmp_lt, htmp_nd,
            hmrk_zero, hmrk_pos, hcov, hsub_rev, hnil_taut, hunit_r⟩,
          fun _ => by rw [← hpc_inv, parseClauseAux_eq_nextLitPure, hnl],
          (fun hc => by cases hc), hm'_a⟩
    | endClause rest =>
      intro j m' hij hj hdrop hm'; p_lets; refine wp_head_jnz_iff (by c0_val_eq) ?_
      refine ⟨fun h => (by cases h), fun _ => ?_⟩
      p_lets; refine wp_head_jnz_iff (by c0_val_eq) ?_
      refine ⟨fun _ => ?_, fun h => (by cases h)⟩
      let st_d := { st with d_cur := cnf_ptr + BitVec.ofNat 64 j, d_val := 0#64 }
      have hm'_a : (bytes cnf_ptr cnfBytes ⋆ PlainMem c st_d ⋆ R) m' := by
        rw [plainMem_eq_dimacs_sep, plainRest_d_irrel]; exact sep_ac hm'
      p_lets
      refine hB1 (BitVec.ofNat 32 tlen, taut_v, false, ()) m'
        ⟨j, tlen, revLits, mrk', tmp', cnf_ptr + BitVec.ofNat 64 j, 0#64, rfl,
          ⟨by omega, hj, htlen_le, hmkl, htmpl, htmp_lt, htmp_nd,
            hmrk_zero, hmrk_pos, hcov, hsub_rev, hnil_taut, hunit_r⟩,
          (fun hc => by cases hc),
          fun _ => ⟨by omega, rfl, by
            rw [← hpc_inv, parseClauseAux_eq_nextLitPure, hnl, List.map_reverse, hdrop]⟩,
          hm'_a⟩
    | lit l rest =>
      intro j m' hl_mv hl_bd hij hj hdrop hm'; p_lets
      refine wp_head_jnz_iff (by c0_val_eq) ?_
      refine ⟨fun h => (by cases h), fun _ => ?_⟩
      p_lets; refine wp_head_jnz_iff (by c0_val_eq) ?_
      refine ⟨fun h => (by cases h), fun _ => ?_⟩
      let st_d := { st with d_cur := cnf_ptr + BitVec.ofNat 64 j, d_val := BitVec.ofNat 64 l }
      have hm'_a : (PlainMem c st_d ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m' := by
        rw [plainMem_eq_dimacs_sep, plainRest_d_irrel]; exact sep_ac hm'
      p_lets
      refine wp_load_of (load_arena_val hm'_a) ?_; p_lets
      refine wp_load_of (load_arena_mv hm'_a) ?_; p_lets
      have hl32 : l < 2 ^ 32 := by omega
      have hv_lt : l / 2 < c.mv := by omega
      have hmvd : st_d.d_val = BitVec.ofNat 64 l := rfl
      rw [hmvd, bv64_trunc32_ofNat hl32, bv32_zext64_eq, bv32_lshr1, bv32_ofNat_toNat hl32]
      have hgd_v : (BitVec.ofNat 64 c.mv).ule (BitVec.ofNat 64 (l / 2)) =
          decide (c.mv ≤ l / 2) := bv_ule_eq (by omega) (by omega)
      refine wp_head_jnz_iff (b := false)
        (by simp only [Arg.val_var, hgd_v]; simp [hv_lt]) ?_
      refine ⟨fun h => (by cases h), fun _ => ?_⟩
      p_lets
      rw [bv32_zext64_eq, bv32_lshr1, bv32_ofNat_toNat hl32]
      have hmkl_d : l / 2 < st_d.mrk.length := by dsimp [st_d, st, st_r]; rw [hmkl]; exact hv_lt
      refine wp_load_of (load_arena_mrk hmkl_d hm'_a) ?_; p_lets
      let mv_b := mrk'[l / 2]'(by rw [hmkl]; exact hv_lt)
      have hmv_b_eq : st_d.mrk[l / 2]'hmkl_d = mv_b := rfl
      rw [hmv_b_eq]
      have hpc_next : parseClauseAux ((cnfBytes.drop j).length + 1) c.mv
          ((l :: revLits).map kissatLitToDimacsLiteral) (cnfBytes.drop j) =
          parseClause c.mv (cnfBytes.drop i0) := by
        have hstep : parseClauseAux ((cnfBytes.drop idx).length + 1) c.mv
            (revLits.map kissatLitToDimacsLiteral) (cnfBytes.drop idx) =
            parseClauseAux (cnfBytes.drop idx).length c.mv
              ((l :: revLits).map kissatLitToDimacsLiteral) (cnfBytes.drop j) := by
          rw [parseClauseAux_eq_nextLitPure, hnl, ← hdrop]; rfl
        rw [← hpc_inv, hstep]
        exact parseClauseAux_fuel_irrel (by simp only [List.length_drop]; omega)
          (by simp only [List.length_drop]; omega)
      refine wp_join_group
        (fun (tl', taut', _err', ()) m_s =>
          ∃ tlen' mrk_n tmp_n, tl' = BitVec.ofNat 32 tlen' ∧
            let st_n := st_r (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 l) mrk_n tmp_n
            IngestReadInv c cnfBytes i0 j tlen' taut' (l :: revLits) st_n ∧
            (bytes cnf_ptr cnfBytes ⋆ PlainMem c st_n ⋆ R) m_s)
        (fun _ ⟨tl', taut', _err', ⟨⟩⟩ m_s ⟨tlen', mrk_n, tmp_n, htl', hinv_n, hm_n⟩ => by
          subst htl'; p_lets
          exact ih1 (cnfBytes.length - j) _ m_s (by omega)
            ⟨j, tlen', l :: revLits, mrk_n, tmp_n, BitVec.ofNat 64 l, rfl, rfl,
              hinv_n, hpc_next, hm_n⟩)
        (fun Js hJs => by
          p_lets; rw [wp_jnz]
          simp only [Arg.val_var, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, bv8_zext32_eq_zero]
          refine ⟨fun hm0 => ?_, fun hmne0 => ?_⟩
          · have hm0' : mrk'[l / 2]'(by rw [hmkl]; exact hv_lt) = 0#8 := hm0
            have hmiss_v : ∀ k < tlen, (tmp'[k]?.getD 0#32).toNat / 2 ≠ l / 2 := by
              intro k hk heq
              have hpos := hmrk_pos k hk
              dsimp only [st_r] at heq hpos
              rw [heq, List.getElem?_eq_getElem (by rw [hmkl]; exact hv_lt),
                Option.getD_some, hm0'] at hpos
              have h1 := congrArg BitVec.toNat hpos
              simp only [BitVec.toNat_ofNat] at h1; omega
            have htlen_lt : tlen < c.mv :=
              inj_lt_of_missing (fun k => (tmp'[k]?.getD 0#32).toNat / 2)
                htmp_nd (fun k hk => by
                  have := htmp_lt k hk; dsimp only [st_r] at this; omega)
                hv_lt hmiss_v
            p_lets; refine wp_load_of (load_arena_mv hm'_a) ?_; p_lets
            rw [bv32_zext64_eq, bv32_ofNat_toNat (by omega)]
            have hgd_t : (BitVec.ofNat 64 c.mv).ule (BitVec.ofNat 64 tlen) =
                decide (c.mv ≤ tlen) := bv_ule_eq (by omega) (by omega)
            refine wp_head_jnz_iff (b := false)
              (by simp only [Arg.val_var, hgd_t]; simp [htlen_lt]) ?_
            refine ⟨fun h => (by cases h), fun _ => ?_⟩
            p_lets
            rw [bv32_zext64_eq, bv32_lshr1, bv32_ofNat_toNat hl32, bv32_ptag_ofNat hl32]
            have hmkl_d2 : l / 2 < st_d.mrk.length := hmkl_d
            obtain ⟨okm, hmm⟩ := store_arena_mrk (i := l / 2) (BitVec.ofNat 8 (l % 2 + 1))
              hmkl_d2 hm'_a
            refine ⟨okm, ?_⟩; p_lets
            rw [bv32_zext64_eq, bv32_ofNat_toNat (by omega), bv64_mul4_nat]
            have htmpl_d : tlen < ({ st_d with
                mrk := st_d.mrk.set (l / 2) (BitVec.ofNat 8 (l % 2 + 1)) }).tmp.length := by
              dsimp [st_d, st, st_r]; rw [htmpl]; exact htlen_lt
            obtain ⟨okt, hmt⟩ := store_arena_tmp (i := tlen) (BitVec.ofNat 32 l) htmpl_d hmm
            refine ⟨okt, ?_⟩; p_lets
            rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
              show BitVec.ofNat 32 tlen + BitVec.ofNat 32 1 =
                BitVec.ofNat 32 (tlen + 1) by bv_omega]
            let mrk_n := mrk'.set (l / 2) (BitVec.ofNat 8 (l % 2 + 1))
            let tmp_n := tmp'.set tlen (BitVec.ofNat 32 l)
            have heq_st : ({ st_d with
                mrk := st_d.mrk.set (l / 2) (BitVec.ofNat 8 (l % 2 + 1)),
                tmp := st_d.tmp.set tlen (BitVec.ofNat 32 l) } : PlainState) =
                st_r (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 l) mrk_n tmp_n := rfl
            rw [heq_st] at hmt
            exact hJs _ _ ⟨tlen + 1, mrk_n, tmp_n, rfl,
              ingestReadInv_push (cnf_ptr := cnf_ptr) (by omega) hj htlen_lt hmkl htmpl hl_mv
                hl32 hv_lt hmiss_v
                ⟨hi_le, hidx, htlen_le, hmkl, htmpl, htmp_lt, htmp_nd, hmrk_zero, hmrk_pos,
                  hcov, hsub_rev, hnil_taut, hunit_r⟩,
              sep_ac hmt⟩
          · have hex : ∃ k0 < tlen, (tmp'[k0]?.getD 0#32).toNat / 2 = l / 2 := by
              by_cases h : ∃ k0 < tlen, (tmp'[k0]?.getD 0#32).toNat / 2 = l / 2
              · exact h
              · exfalso
                have h0 := hmrk_zero (l / 2) hv_lt (fun k hk heq => by
                  dsimp only [st_r] at heq; exact h ⟨k, hk, heq⟩)
                dsimp only [st_r] at h0
                rw [List.getElem?_eq_getElem (by rw [hmkl]; exact hv_lt),
                  Option.getD_some] at h0; exact hmne0 h0
            obtain ⟨k0, hk0, hk0_v⟩ := hex
            have hmv_pos := hmrk_pos k0 hk0
            dsimp only [st_r] at hmv_pos
            rw [hk0_v, List.getElem?_eq_getElem (by rw [hmkl]; exact hv_lt),
              Option.getD_some] at hmv_pos
            refine wp_join_group
              (fun (taut', ()) m_j =>
                (taut' = if mv_b = BitVec.ofNat 8 (l % 2 + 1) then taut_v else true) ∧ m_j = m')
              (fun _ ⟨taut', ⟨⟩⟩ m_j ⟨htaut', hm_j⟩ => by
                subst m_j; p_lets
                refine hJs _ m' ⟨tlen, mrk', tmp', rfl,
                    ⟨by omega, hj, htlen_le, hmkl, htmpl, htmp_lt, htmp_nd, hmrk_zero, hmrk_pos,
                      ingest_dup_cov hmkl hv_lt hk0 htaut' rfl hmv_pos hcov hk0_v,
                      (fun k hk => List.mem_cons_of_mem _ (hsub_rev k hk)), (fun hc => by cases hc),
                      fun l' hl' => by
                        rcases List.cons.inj hl' with ⟨_, rfl⟩
                        dsimp only [st_r] at hsub_rev; exact absurd (hsub_rev k0 hk0) (by simp)⟩,
                    sep_ac hm'_a⟩)
              (fun Jt hJt => by
                p_lets; rw [wp_jnz]
                simp only [Arg.val_var, bv32_ptag_ofNat hl32, bv8_zext32_bne,
                  decide_eq_true_eq, decide_eq_false_iff_not, Classical.not_not]
                refine ⟨fun hne => hJt (true, ()) m' ⟨by simp [hne], rfl⟩,
                  fun heq => hJt (taut_v, ()) m' ⟨by simp [heq], rfl⟩⟩))
  · intro B1 L1 _ hL1; p_lets
    exact hL1 (cnfBytes.length - i0) _ m
      ⟨i0, 0, [], s.mrk, s.tmp, s.d_val, rfl, rfl,
        ⟨Nat.le_refl _, hi0, Nat.zero_le _, hlen.mrk_len, hlen.tmp_len_arr,
          fun _ h => by omega, fun _ _ h => by omega,
          fun v hv _ => hinv.marks v hv, fun _ h => by omega,
          (fun _ _ h => by cases h), (fun _ h => by omega), (fun _ => rfl),
          (fun _ h => by cases h)⟩,
        by unfold parseClause; simp, by rw [hst0]; exact hm⟩

end LeanQbe.T.Examples.Kissat.Plain
