module

public import LeanQbe.T.Examples.Kissat.FullFastCore
public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.FullPropDecLemmas
public import LeanQbe.T.Logic.C0HeadStep
public import LeanQbe.T.Logic.ControlComb
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` M2 Fast BCP Helpers & Building Blocks (`FullFastCoreBcpLemmas1`)

Proves canonical `FullSpec2`-compatible `Func.wp` contracts for the M2 Fast BCP core:
1. `full_prop_lit_wp` (`FullSpec2.fullPropLitSpec`): inline value check & two-pass replacement
   search (`srch`), non-chronological `nl_lvl == cur_lvl` fast path, delayed header sync
   (`trail_end`, `unassigned`, `unflushed`, `search_ticks`), and zero dead watch-tail sentinel loop.
2. `full_propagate_ignore_wp` (`FullSpec2.fullPropagateIgnoreSpec`): register-cached `prop`/`fuel`
   with eager `h->propagated = prop` and delayed exit `h->fuel = fuel`.
3. `full_propagate_wp` (`FullSpec2.fullPropagateSpec`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FastCore

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test
open LeanQbe.T.Examples.Kissat.Full hiding
  full_prop_lit_body full_prop_lit_wf full_prop_lit_wp
  full_propagate_ignore_body full_propagate_ignore_wf full_propagate_ignore_wp
  full_propagate_body full_propagate_wf full_propagate_wp
open LeanQbe.T.Examples.Kissat.Full.FullPropDecSpecs hiding
  fullPropLitSpec fullPropagateIgnoreSpec fullPropagateSpec fullWatchPushSpec
  FullTrailExt FullArenaPermEq
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics

/-! ## 1. Stepper Macros & Delayed Header Sync Helpers -/

local macro "fc_hsteps" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsteps))

theorem fc_wp_head_eq {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {e1 e2 : Expr Val Cont rs} (h : e1 = e2) (hk : wp Γ Q X e2 m) :
    wp Γ Q X e1 m := h ▸ hk

theorem fc_wp_let_head {Γ : Env} {rs sig ts : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {c : OpCode sig ts} {args : Tup (Arg Val) sig}
    {k : Tup Val ts → Expr Val Cont rs} {r : Tup Val ts}
    (hr : ∀ P, P r → c.wp (vals args) P) (hk : wp Γ Q X (k r) m) :
    wp Γ Q X (.let_ (Op.mk c args) k) m := hr _ hk

theorem fc_wp_blocks_here {Γ : Env} {rs ts : List Ty} {sig : List (List Ty)}
    {Q : Post rs} {X : XPost} {m : Mem 64}
    {b : Tup Val ts → Expr Val Cont rs} {bs : Blocks Val Cont rs sig} {xs : Tup Val ts}
    (h : wp Γ Q X (b xs) m) : wp Γ Q X (Blocks.get (Blocks.cons b bs) .here xs) m := h

theorem fc_wp_ret_head {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {xs : Tup (Arg Val) rs} (h : Q (vals xs) m) : wp Γ Q X (.ret xs) m := h

theorem fc_wp_jump_head {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {J : Cont ts} {xs : Tup (Arg Val) ts}
    (h : J (vals xs) m) : wp Γ Q X (.jump J xs) m := h

section FastLet
variable {Γ : Env} {rs : List Ty} {n : Nat} {Q : Post rs} {X : XPost} {m : Mem 64}
theorem fc_let_add {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (va + vb, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.add (.bits n)) (a, b, ())) k) m := by cases ha; cases hb; exact hk
theorem fc_let_sub {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (va - vb, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.sub (.bits n)) (a, b, ())) k) m := by cases ha; cases hb; exact hk
theorem fc_let_mul {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (va * vb, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.mul (.bits n)) (a, b, ())) k) m := by cases ha; cases hb; exact hk
theorem fc_let_and {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (va &&& vb, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.and (.bits n)) (a, b, ())) k) m := by cases ha; cases hb; exact hk
theorem fc_let_or {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (va ||| vb, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.or (.bits n)) (a, b, ())) k) m := by cases ha; cases hb; exact hk
theorem fc_let_xor {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (va ^^^ vb, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.xor (.bits n)) (a, b, ())) k) m := by cases ha; cases hb; exact hk
theorem fc_let_eq {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (va == vb, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .eq (.bits n)) (a, b, ())) k) m := by
  cases ha; cases hb
  simpa only [wp, Op.wp, OpCode.wp, vals, liftCmp, evalBits_eq_beq, Ty.hasFloat,
    Bool.false_eq_true, ite_false] using hk
theorem fc_let_ne {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (va != vb, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .ne (.bits n)) (a, b, ())) k) m := by
  cases ha; cases hb
  simpa only [wp, Op.wp, OpCode.wp, vals, liftCmp, evalBits_ne_bne, Ty.hasFloat,
    Bool.false_eq_true, ite_false] using hk
theorem fc_let_ult {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (va.ult vb, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .ult (.bits n)) (a, b, ())) k) m := by cases ha; cases hb; exact hk
theorem fc_let_ule {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (va.ule vb, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .ule (.bits n)) (a, b, ())) k) m := by cases ha; cases hb; exact hk
theorem fc_let_ugt {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (vb.ult va, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .ugt (.bits n)) (a, b, ())) k) m := by cases ha; cases hb; exact hk
theorem fc_let_uge {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (vb.ule va, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .uge (.bits n)) (a, b, ())) k) m := by cases ha; cases hb; exact hk
theorem fc_let_slt {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (va.slt vb, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .slt (.bits n)) (a, b, ())) k) m := by cases ha; cases hb; exact hk
theorem fc_let_sle {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (va.sle vb, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .sle (.bits n)) (a, b, ())) k) m := by cases ha; cases hb; exact hk
theorem fc_let_sgt {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (vb.slt va, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .sgt (.bits n)) (a, b, ())) k) m := by cases ha; cases hb; exact hk
theorem fc_let_sge {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (vb.sle va, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .sge (.bits n)) (a, b, ())) k) m := by cases ha; cases hb; exact hk
theorem fc_let_zext32_64 {a : Arg Val i32} {va : BitVec 32} {k} (ha : a.val = va)
    (hk : wp Γ Q X (k (va.setWidth 64, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.zext 32 64) (a, ())) k) m := by cases ha; exact ⟨by decide, hk⟩
theorem fc_let_sext8_32 {a : Arg Val i8} {va : BitVec 8} {k} (ha : a.val = va)
    (hk : wp Γ Q X (k (va.signExtend 32, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.sext 8 32) (a, ())) k) m := by cases ha; exact ⟨by decide, hk⟩
theorem fc_let_trunc64_32 {a : Arg Val i64} {va : BitVec 64} {k} (ha : a.val = va)
    (hk : wp Γ Q X (k (va.setWidth 32, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.trunc 64 32) (a, ())) k) m := by cases ha; exact ⟨by decide, hk⟩
theorem fc_let_shl64_1 {a b : Arg Val i64} {va : BitVec 64} {k} (ha : a.val = va)
    (hb : b.val = 1#64) (hk : wp Γ Q X (k (va <<< (1 : Nat), ())) m) :
    wp Γ Q X (.let_ (Op.mk (.shl i64) (a, b, ())) k) m := by
  cases ha
  simpa only [wp, Op.wp, OpCode.wp, vals, lift2, hb, BitVec.reduceToNat, Nat.reduceMod,
    Ty.hasFloat, Bool.false_eq_true, ite_false] using hk
theorem fc_let_lshr32_1 {a b : Arg Val i32} {va : BitVec 32} {k} (ha : a.val = va)
    (hb : b.val = 1#32) (hk : wp Γ Q X (k (va >>> (1 : Nat), ())) m) :
    wp Γ Q X (.let_ (Op.mk (.lshr i32) (a, b, ())) k) m := by
  cases ha
  simpa only [wp, Op.wp, OpCode.wp, vals, lift2, hb, BitVec.reduceToNat, Nat.reduceMod,
    Ty.hasFloat, Bool.false_eq_true, ite_false] using hk
end FastLet

theorem fc_bv64_shl1_u32_nat (x : BitVec 32) :
    (x.setWidth 64 <<< (1 : Nat)).toNat = 2 * x.toNat := bv64_shl1_u32 x

theorem fc_bv64_shl1_add1_nat (x : BitVec 32) :
    ((x.setWidth 64 <<< (1 : Nat)) + (1 : BitVec 64)).toNat = 2 * x.toNat + 1 := by
  have hx := x.isLt
  rw [bv64_add1_toNat (by rw [fc_bv64_shl1_u32_nat]; omega), fc_bv64_shl1_u32_nat]

theorem fc_bv64_ofNat_toNat (n : Nat) :
    (OfNat.ofNat n : BitVec 64).toNat = n % 2 ^ 64 := rfl

theorem fc_bv32_ofNat_toNat (n : Nat) :
    (OfNat.ofNat n : BitVec 32).toNat = n % 2 ^ 32 := rfl

theorem fc_nat_xor_one (x : Nat) :
    x ^^^ 1 = if x % 2 = 0 then x + 1 else x - 1 := by
  simpa [litNeg] using litNeg_eq x

theorem fc_getElem_eq_of_idx {α : Type} {xs : List α} {i j : Nat}
    (hij : i = j) (hi : i < xs.length) (hj : j < xs.length) :
    xs[i]'hi = xs[j]'hj := by subst hij; rfl

theorem fc_getElem_eq_getD_of_idx {n : Nat} {xs : List (BitVec n)} {i j : Nat}
    (hij : i = j) (hi : i < xs.length) :
    xs[i]'hi = xs[j]?.getD 0 := by
  subst hij; rw [List.getElem?_eq_getElem hi, Option.getD_some]

/-- Memory-resident shadow of logical propagation state `sem`: holds `trail_end`, `unassigned`,
`unflushed`, and `search_ticks` equal to entry state `s0` until `full_prop_lit` exits. -/
def fastPropMem (s0 sem : FullState) : FullState :=
  { sem with
    core := { sem.core with
      trail_end := s0.core.trail_end
      unassigned := s0.core.unassigned
      unflushed := s0.core.unflushed }
    scratch := { sem.scratch with search_ticks := s0.scratch.search_ticks } }

theorem fastPropMem_def (s0 sem : FullState) :
    fastPropMem s0 sem =
      { sem with
        core := { sem.core with
          trail_end := s0.core.trail_end
          unassigned := s0.core.unassigned
          unflushed := s0.core.unflushed }
        scratch := { sem.scratch with search_ticks := s0.scratch.search_ticks } } := rfl

theorem fastPropMem_vals (s0 sem : FullState) :
    (fastPropMem s0 sem).core.vals = sem.core.vals := rfl
theorem fastPropMem_flags (s0 sem : FullState) :
    (fastPropMem s0 sem).core.flags = sem.core.flags := rfl
theorem fastPropMem_lvl (s0 sem : FullState) :
    (fastPropMem s0 sem).core.lvl = sem.core.lvl := rfl
theorem fastPropMem_rsns (s0 sem : FullState) :
    (fastPropMem s0 sem).core.rsns = sem.core.rsns := rfl
theorem fastPropMem_trl (s0 sem : FullState) :
    (fastPropMem s0 sem).core.trl = sem.core.trl := rfl
theorem fastPropMem_trail_pos (s0 sem : FullState) :
    (fastPropMem s0 sem).core.trail_pos = sem.core.trail_pos := rfl
theorem fastPropMem_wvec (s0 sem : FullState) :
    (fastPropMem s0 sem).core.wvec = sem.core.wvec := rfl
theorem fastPropMem_arena (s0 sem : FullState) :
    (fastPropMem s0 sem).core.arena = sem.core.arena := rfl
theorem fastPropMem_wstk (s0 sem : FullState) :
    (fastPropMem s0 sem).core.wstk = sem.core.wstk := rfl
theorem fastPropMem_phases (s0 sem : FullState) :
    (fastPropMem s0 sem).scratch.phases = sem.scratch.phases := rfl
theorem fastPropMem_cur_vars (s0 sem : FullState) :
    (fastPropMem s0 sem).core.cur_vars = sem.core.cur_vars := rfl
theorem fastPropMem_cur_level (s0 sem : FullState) :
    (fastPropMem s0 sem).core.cur_level = sem.core.cur_level := rfl
theorem fastPropMem_arena_len (s0 sem : FullState) :
    (fastPropMem s0 sem).core.arena_len = sem.core.arena_len := rfl
theorem fastPropMem_oom (s0 sem : FullState) :
    (fastPropMem s0 sem).core.oom = sem.core.oom := rfl
theorem fastPropMem_wlen (s0 sem : FullState) :
    (fastPropMem s0 sem).core.wlen = sem.core.wlen := rfl
theorem fastPropMem_wusable (s0 sem : FullState) :
    (fastPropMem s0 sem).core.wusable = sem.core.wusable := rfl
theorem fastPropMem_probing (s0 sem : FullState) :
    (fastPropMem s0 sem).core.probing = sem.core.probing := rfl
theorem fastPropMem_propagated (s0 sem : FullState) :
    (fastPropMem s0 sem).core.propagated = sem.core.propagated := rfl
theorem fastPropMem_trail_end (s0 sem : FullState) :
    (fastPropMem s0 sem).core.trail_end = s0.core.trail_end := rfl
theorem fastPropMem_unassigned (s0 sem : FullState) :
    (fastPropMem s0 sem).core.unassigned = s0.core.unassigned := rfl
theorem fastPropMem_unflushed (s0 sem : FullState) :
    (fastPropMem s0 sem).core.unflushed = s0.core.unflushed := rfl
theorem fastPropMem_search_ticks (s0 sem : FullState) :
    (fastPropMem s0 sem).scratch.search_ticks = s0.scratch.search_ticks := rfl
theorem fastPropMem_wsort (s0 sem : FullState) :
    (fastPropMem s0 sem).scratch.wsort = sem.scratch.wsort := rfl
theorem fastPropMem_watchSize (s0 sem : FullState) (l : Nat) :
    fullWatchSizeCore (fastPropMem s0 sem).core l = fullWatchSizeCore sem.core l := rfl
theorem fastPropMem_watchOff (s0 sem : FullState) (l : Nat) :
    fullWatchOffCore (fastPropMem s0 sem).core l = fullWatchOffCore sem.core l := rfl

theorem fastPropMem_with_wstk (s0 sem : FullState) (w' : List (BitVec 32)) :
    { fastPropMem s0 sem with core := { (fastPropMem s0 sem).core with wstk := w' } } =
      fastPropMem s0 { sem with core := { sem.core with wstk := w' } } := rfl

theorem fastPropMem_with_arena (s0 sem : FullState) (a' : List (BitVec 32)) :
    { fastPropMem s0 sem with core := { (fastPropMem s0 sem).core with arena := a' } } =
      fastPropMem s0 { sem with core := { sem.core with arena := a' } } := rfl

theorem fastPropMem_with_bin_confl (s0 sem : FullState) (l0 l1 : BitVec 64) :
    { fastPropMem s0 sem with
      core := { (fastPropMem s0 sem).core with
        confl_type := 1#64, confl_lit0 := l0, confl_lit1 := l1, confl_ref := 0xFFFFFFFF#64 } } =
      fastPropMem s0 { sem with
        core := { sem.core with
          confl_type := 1#64, confl_lit0 := l0, confl_lit1 := l1,
          confl_ref := 0xFFFFFFFF#64 } } := rfl

theorem fastPropMem_with_bin_confl_wstk (s0 sem : FullState)
    (l0 l1 : BitVec 64) (ws' : List (BitVec 32)) :
    { fastPropMem s0 sem with
      core := { (fastPropMem s0 sem).core with
        confl_type := 1#64, confl_lit0 := l0, confl_lit1 := l1,
        confl_ref := 0xFFFFFFFF#64, wstk := ws' } } =
      fastPropMem s0 { sem with
        core := { sem.core with
          confl_type := 1#64, confl_lit0 := l0, confl_lit1 := l1,
          confl_ref := 0xFFFFFFFF#64, wstk := ws' } } := rfl

theorem fastPropMem_with_large_confl_wstk (s0 sem : FullState)
    (cr : BitVec 64) (ws' : List (BitVec 32)) :
    { fastPropMem s0 sem with
      core := { (fastPropMem s0 sem).core with
        confl_type := 2#64, confl_ref := cr, wstk := ws' } } =
      fastPropMem s0 { sem with
        core := { sem.core with confl_type := 2#64, confl_ref := cr, wstk := ws' } } := rfl

theorem fastPropMem_with_large_confl (s0 sem : FullState) (cr : BitVec 64) :
    { fastPropMem s0 sem with
      core := { (fastPropMem s0 sem).core with confl_type := 2#64, confl_ref := cr } } =
      fastPropMem s0 { sem with
        core := { sem.core with confl_type := 2#64, confl_ref := cr } } := rfl

theorem fastPropMem_with_push (s0 st3 : FullState)
    (wv' ws' : List (BitVec 32)) (wl' : Nat) (wu' : BitVec 64) (wso' : List (BitVec 32)) :
    FullState.mk
      { (fastPropMem s0 st3).core with wvec := wv', wstk := ws', wlen := wl', wusable := wu' }
      { (fastPropMem s0 st3).scratch with wsort := wso' } =
      fastPropMem s0 (FullState.mk
        { st3.core with wvec := wv', wstk := ws', wlen := wl', wusable := wu' }
        { st3.scratch with wsort := wso' }) := rfl

theorem fastPropMem_with_push_core (s0 st3 : FullState)
    (wv' ws' : List (BitVec 32)) (wl' : Nat) (wu' : BitVec 64) (wso' : List (BitVec 32)) :
    { (fastPropMem s0 st3).core with wvec := wv', wstk := ws', wlen := wl', wusable := wu' } =
      (fastPropMem s0 (FullState.mk
        { st3.core with wvec := wv', wstk := ws', wlen := wl', wusable := wu' }
        { st3.scratch with wsort := wso' })).core := rfl

theorem fastPropMem_with_push_rec (s0 st3 : FullState)
    (wv' ws' : List (BitVec 32)) (wl' : Nat) (wu' : BitVec 64) (wso' : List (BitVec 32)) :
    { fastPropMem s0 st3 with
      core := { (fastPropMem s0 st3).core with
        wvec := wv', wstk := ws', wlen := wl', wusable := wu' }
      scratch := { (fastPropMem s0 st3).scratch with wsort := wso' } } =
      fastPropMem s0 { st3 with
        core := { st3.core with
          wvec := wv', wstk := ws', wlen := wl', wusable := wu' }
        scratch := { st3.scratch with wsort := wso' } } := by
  unfold fastPropMem; rfl

theorem fastPropMem_with_oom_revert (s0 st4 : FullState)
    (ar' ws' : List (BitVec 32)) :
    { fastPropMem s0 st4 with
      core := { (fastPropMem s0 st4).core with arena := ar', wstk := ws', oom := 1#64 } } =
      fastPropMem s0 { st4 with
        core := { st4.core with arena := ar', wstk := ws', oom := 1#64 } } := rfl

theorem fastPropMem_with_vals_ph (s0 sem : FullState)
    (vs' : List (BitVec 8)) (ph' : List (BitVec 8)) :
    FullState.mk
      { (fastPropMem s0 sem).core with vals := vs' }
      { (fastPropMem s0 sem).scratch with phases := ph' } =
      fastPropMem s0 (FullState.mk
        { sem.core with vals := vs' }
        { sem.scratch with phases := ph' }) := rfl

theorem fastPropMem_assign_eq (s0 sem1 : FullState)
    (vs' : List (BitVec 8)) (fl' lv' rs' tp' tr' : List (BitVec 32))
    (ph' : List (BitVec 8)) (te' : Nat) (un' uf' : BitVec 64) :
    FullState.mk
      { (fastPropMem s0 sem1).core with
        vals := vs', flags := fl', lvl := lv', rsns := rs', trail_pos := tp', trl := tr' }
      { (fastPropMem s0 sem1).scratch with phases := ph' } =
      fastPropMem s0 (FullState.mk
        { sem1.core with
          vals := vs', flags := fl', lvl := lv', rsns := rs', trl := tr', trail_pos := tp',
          trail_end := te', unassigned := un', unflushed := uf' }
        { sem1.scratch with phases := ph' }) := rfl

theorem fastPropMem_finish_eq (s0 sem : FullState)
    (ws' wv' : List (BitVec 32)) (wu' ticks' : BitVec 64) :
    FullState.mk
      { (fastPropMem s0 { sem with core := { sem.core with wstk := ws' } }).core with
        wvec := wv', wusable := wu', trail_end := sem.core.trail_end,
        unassigned := sem.core.unassigned, unflushed := sem.core.unflushed }
      { (fastPropMem s0 { sem with core := { sem.core with wstk := ws' } }).scratch with
        search_ticks := ticks' } =
      FullState.mk
        { sem.core with wstk := ws', wvec := wv', wusable := wu' }
        { sem.scratch with search_ticks := ticks' } := rfl

theorem fastPropMem_with_vals (s0 sem : FullState) (vs' : List (BitVec 8)) :
    { fastPropMem s0 sem with core := { (fastPropMem s0 sem).core with vals := vs' } } =
      fastPropMem s0 { sem with core := { sem.core with vals := vs' } } := rfl

theorem fastPropMem_with_vals_fl_lv_rs (s0 sem : FullState)
    (vs' : List (BitVec 8)) (fl' lv' rs' : List (BitVec 32)) (ph' : List (BitVec 8)) :
    FullState.mk
      { (fastPropMem s0 sem).core with vals := vs', flags := fl', lvl := lv', rsns := rs' }
      { (fastPropMem s0 sem).scratch with phases := ph' } =
      fastPropMem s0 (FullState.mk
        { sem.core with vals := vs', flags := fl', lvl := lv', rsns := rs' }
        { sem.scratch with phases := ph' }) := rfl

theorem fastPropMem_self (s : FullState) : fastPropMem s s = s := by
  cases s with | mk c sc => cases c; cases sc; rfl

theorem fc_getElem_vals (s0 sem : FullState) {i : Nat}
    {hi : i < (fastPropMem s0 sem).core.vals.length} :
    (fastPropMem s0 sem).core.vals[i]'hi = sem.core.vals[i]'(fastPropMem_vals s0 sem ▸ hi) := rfl
theorem fc_getElem_flags (s0 sem : FullState) {i : Nat}
    {hi : i < (fastPropMem s0 sem).core.flags.length} :
    (fastPropMem s0 sem).core.flags[i]'hi = sem.core.flags[i]'(fastPropMem_flags s0 sem ▸ hi) :=
  rfl
theorem fc_getElem_lvl (s0 sem : FullState) {i : Nat}
    {hi : i < (fastPropMem s0 sem).core.lvl.length} :
    (fastPropMem s0 sem).core.lvl[i]'hi = sem.core.lvl[i]'(fastPropMem_lvl s0 sem ▸ hi) := rfl
theorem fc_getElem_rsns (s0 sem : FullState) {i : Nat}
    {hi : i < (fastPropMem s0 sem).core.rsns.length} :
    (fastPropMem s0 sem).core.rsns[i]'hi = sem.core.rsns[i]'(fastPropMem_rsns s0 sem ▸ hi) := rfl
theorem fc_getElem_trl (s0 sem : FullState) {i : Nat}
    {hi : i < (fastPropMem s0 sem).core.trl.length} :
    (fastPropMem s0 sem).core.trl[i]'hi = sem.core.trl[i]'(fastPropMem_trl s0 sem ▸ hi) := rfl
theorem fc_getElem_trail_pos (s0 sem : FullState) {i : Nat}
    {hi : i < (fastPropMem s0 sem).core.trail_pos.length} :
    (fastPropMem s0 sem).core.trail_pos[i]'hi =
      sem.core.trail_pos[i]'(fastPropMem_trail_pos s0 sem ▸ hi) := rfl
theorem fc_getElem_wvec (s0 sem : FullState) {i : Nat}
    {hi : i < (fastPropMem s0 sem).core.wvec.length} :
    (fastPropMem s0 sem).core.wvec[i]'hi = sem.core.wvec[i]'(fastPropMem_wvec s0 sem ▸ hi) := rfl
theorem fc_getElem_arena (s0 sem : FullState) {i : Nat}
    {hi : i < (fastPropMem s0 sem).core.arena.length} :
    (fastPropMem s0 sem).core.arena[i]'hi = sem.core.arena[i]'(fastPropMem_arena s0 sem ▸ hi) :=
  rfl
theorem fc_getElem_wstk (s0 sem : FullState) {i : Nat}
    {hi : i < (fastPropMem s0 sem).core.wstk.length} :
    (fastPropMem s0 sem).core.wstk[i]'hi = sem.core.wstk[i]'(fastPropMem_wstk s0 sem ▸ hi) := rfl
theorem fc_getElem_phases (s0 sem : FullState) {i : Nat}
    {hi : i < (fastPropMem s0 sem).scratch.phases.length} :
    (fastPropMem s0 sem).scratch.phases[i]'hi =
      sem.scratch.phases[i]'(fastPropMem_phases s0 sem ▸ hi) := rfl

attribute [local irreducible] fastPropMem

open Lean Elab Tactic in
meta def fcHeadRun (stopAtJnz : Bool) : TacticM Unit := do
  let binOps : Array (Lean.Name × Lean.Name) := #[
    (``OpCode.add, ``fc_let_add), (``OpCode.sub, ``fc_let_sub), (``OpCode.mul, ``fc_let_mul),
    (``OpCode.and, ``fc_let_and), (``OpCode.or, ``fc_let_or), (``OpCode.xor, ``fc_let_xor),
    (``OpCode.eq, ``fc_let_eq), (``CmpOp.eq, ``fc_let_eq), (``OpCode.ne, ``fc_let_ne),
    (``CmpOp.ne, ``fc_let_ne), (``OpCode.ult, ``fc_let_ult), (``CmpOp.ult, ``fc_let_ult),
    (``OpCode.ule, ``fc_let_ule), (``CmpOp.ule, ``fc_let_ule), (``OpCode.ugt, ``fc_let_ugt),
    (``CmpOp.ugt, ``fc_let_ugt), (``OpCode.uge, ``fc_let_uge), (``CmpOp.uge, ``fc_let_uge),
    (``OpCode.slt, ``fc_let_slt), (``CmpOp.slt, ``fc_let_slt), (``OpCode.sle, ``fc_let_sle),
    (``CmpOp.sle, ``fc_let_sle), (``OpCode.sgt, ``fc_let_sgt), (``CmpOp.sgt, ``fc_let_sgt),
    (``OpCode.sge, ``fc_let_sge), (``CmpOp.sge, ``fc_let_sge)]
  let unOps : Array (Lean.Name × Lean.Name) := #[
    (``OpCode.zext, ``fc_let_zext32_64), (``OpCode.sext, ``fc_let_sext8_32),
    (``OpCode.trunc, ``fc_let_trunc64_32)]
  let clearSet : Array Lean.Name := #[
    ``Exists, ``Std.ExtHashMap.sep, ``FullMem, ``FullCoreInv, ``FullWitnessInv, ``PropLitInv,
    ``SplitWatchesInv, ``AgreesExcept, ``FullTrailExt, ``FullArenaPermEq,
    ``FullPropDecSpecs.FullTrailExt,
    ``FullPropDecSpecs.FullArenaPermEq, ``FullState.LengthsOk, ``FullCoreState.LengthsOk,
    ``FullScratch.LengthsOk, ``PropLitConfl, ``FullConflictOkW, ``FullPropDecSpecs.FullConflOkW]
  let rec normProj : Nat → Lean.Expr → Lean.Expr
    | 0, x => x
    | n + 1, x =>
      let x := x.consumeMData
      if (x.isAppOf ``Prod.fst || x.isAppOf ``Prod.snd) && x.getAppNumArgs ≥ 3 then
        let p := normProj n (x.getArg! 2)
        if p.isAppOf ``Prod.mk && p.getAppNumArgs ≥ 4 then
          normProj n (p.getArg! (if x.isAppOf ``Prod.fst then 2 else 3))
        else x
      else x
  let argVal (x : Lean.Expr) : Option (Lean.Expr × Bool) :=
    let x := x.consumeMData
    if x.isAppOf ``LeanQbe.T.Arg.var then
      let v := normProj 6 x.appArg!
      some (v, v.isAppOf ``OfNat.ofNat || v.isAppOf ``BitVec.ofNat)
    else if x.isAppOf ``LeanQbe.T.Arg.imm then some (normProj 6 x.appArg!, true)
    else none
  let hdrLoadLems : Array Lean.Name := #[
    ``FullArenaTactics.load_full_arena_len, ``FullArenaTactics.load_full_search_ticks,
    ``FullArenaTactics.load_full_wusable, ``FullArenaTactics.load_full_values_ptr,
    ``FullArenaTactics.load_full_watch_vec_ptr, ``FullArenaTactics.load_full_arena_ptr,
    ``FullArenaTactics.load_full_watch_stk_ptr, ``FullArenaTactics.load_full_level_ptr,
    ``FullArenaTactics.load_full_cur_vars, ``FullArenaTactics.load_full_max_vars,
    ``FullArenaTactics.load_full_reason_ptr, ``FullArenaTactics.load_full_trail_ptr,
    ``FullArenaTactics.load_full_trail_pos_ptr, ``FullArenaTactics.load_full_flags_ptr,
    ``FullArenaTactics.load_full_phases_ptr, ``FullArenaTactics.load_full_trail_end,
    ``FullArenaTactics.load_full_unassigned, ``FullArenaTactics.load_full_unflushed,
    ``FullArenaTactics.load_full_cur_level, ``FullArenaTactics.load_full_probing,
    ``FullArenaTactics.load_full_propagated, ``FullArenaTactics.load_full_fuel,
    ``FullArenaTactics.load_full_oom]
  let hdrStoreLems : Array Lean.Name := #[
    ``FullArenaTactics.store_full_search_ticks, ``FullArenaTactics.store_full_wusable,
    ``FullArenaTactics.store_full_oom, ``FullArenaTactics.store_full_confl_type,
    ``FullArenaTactics.store_full_confl_ref, ``FullArenaTactics.store_full_confl_lit0,
    ``FullArenaTactics.store_full_confl_lit1, ``FullArenaTactics.c0_store_full_trail_end,
    ``FullArenaTactics.store_full_unassigned, ``FullArenaTactics.store_full_unflushed,
    ``FullArenaTactics.c0_store_full_propagated, ``FullArenaTactics.store_full_fuel]
  let pickLems (isLoad : Bool) (ty : Lean.Expr) : Array Lean.Name :=
    if (ty.find? (·.isConstOf ``FullCfg.pWstk)).isSome then
      if isLoad then #[``FullArenaTactics.c0_load_full_wstk]
      else #[``FullArenaTactics.c0_store_full_wstk]
    else if (ty.find? (·.isConstOf ``FullCfg.pArena)).isSome then
      if isLoad then #[``FullArenaTactics.c0_load_full_arena]
      else #[``FullArenaTactics.c0_store_full_arena]
    else if (ty.find? (·.isConstOf ``FullCfg.pVals)).isSome then
      if isLoad then #[``FullArenaTactics.c0_load_full_vals]
      else #[``FullArenaTactics.c0_store_full_vals]
    else if (ty.find? (·.isConstOf ``FullCfg.pWvec)).isSome then
      if isLoad then #[``FullArenaTactics.c0_load_full_wvec]
      else #[``FullArenaTactics.c0_store_full_wvec]
    else if (ty.find? (·.isConstOf ``FullCfg.pLevel)).isSome then
      if isLoad then #[``FullArenaTactics.c0_load_full_lvl]
      else #[``FullArenaTactics.c0_store_full_lvl]
    else if (ty.find? (·.isConstOf ``FullCfg.pFlags)).isSome then
      if isLoad then #[``FullArenaTactics.c0_load_full_flags]
      else #[``FullArenaTactics.c0_store_full_flags]
    else if (ty.find? (·.isConstOf ``FullCfg.pPhases)).isSome then
      if isLoad then #[``FullArenaTactics.c0_load_full_phases]
      else #[``FullArenaTactics.c0_store_full_phases]
    else if (ty.find? (·.isConstOf ``FullCfg.pReason)).isSome then
      if isLoad then #[``FullArenaTactics.c0_load_full_rsns]
      else #[``FullArenaTactics.c0_store_full_rsns]
    else if (ty.find? (·.isConstOf ``FullCfg.pTrail)).isSome then
      if isLoad then #[``FullArenaTactics.c0_load_full_trl]
      else #[``FullArenaTactics.c0_store_full_trl]
    else if (ty.find? (·.isConstOf ``FullCfg.pTrailPos)).isSome then
      if isLoad then #[``FullArenaTactics.c0_load_full_trail_pos]
      else #[``FullArenaTactics.c0_store_full_trail_pos]
    else if isLoad then hdrLoadLems else hdrStoreLems
  let solveMem (isLoad : Bool) (hmv : Lean.MVarId) : TacticM Unit := do
    setGoals [hmv]
    evalTactic
      (← `(tactic| (try simp only [LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm]);
        (try dsimp (config := { zeta := false }) only)))
    let hmv ← getMainGoal
    let lems := pickLems isLoad (← Lean.instantiateMVars (← hmv.getType))
    let mut solved := false
    for nm in lems do
      let s ← saveState
      let ok ← try
        let sub ← Lean.Meta.withReducible <|
          hmv.apply (← Lean.Meta.mkConstWithFreshMVarLevels nm)
        let mut allOk := true
        for g' in sub do
          if !allOk then break
          if (← Lean.instantiateMVars (← g'.getType)).isAppOf ``Std.ExtHashMap.sep then
            setGoals [g']
            Lean.Meta.withReducible <|
              evalTactic (← `(tactic| first | assumption | c0_frame))
            if !(← getUnsolvedGoals).isEmpty then
              allOk := false
        for g' in sub do
          if !allOk || (← g'.isAssigned) then continue
          if ← Lean.Meta.isProp (← g'.getType) then
            setGoals [g']
            evalTactic (← `(tactic| first | rfl | assumption | decide | skip))
            if (← getUnsolvedGoals).isEmpty then continue
            let hidxIds ← (← getMainGoal).withContext do
              let mut ids : Array Lean.Name := #[]
              for d in (← Lean.getLCtx).decls do
                let some d := d | continue
                if d.isAuxDecl || d.isLet then continue
                let nm := d.userName.toString
                if (nm == "hidx_li" || nm == "hidx_r1" || nm == "hidx_r2" ||
                    nm == "h1_idx" || nm == "h3_idx" || nm == "h4_idx") &&
                    (← Lean.instantiateMVars d.type).isAppOf ``Eq then
                  ids := ids.push d.userName
              pure ids
            for nm in hidxIds do
              let fid := Lean.mkIdent nm
              evalTactic (← `(tactic| try simp only [$fid:ident]))
            let g' ← getMainGoal
            let gTy ← Lean.instantiateMVars (← g'.getType)
            let hasGetElem (e : Lean.Expr) : Bool :=
              (e.find? fun x =>
                x.isConstOf ``GetElem.getElem || x.isConstOf ``GetElem?.getElem?).isSome
            let usesGetElem := hasGetElem gTy
            let toClear ← g'.withContext do
              let mut ids : Array Lean.FVarId := #[]
              for d in (← Lean.getLCtx).decls do
                let some d := d | continue
                if d.isAuxDecl || d.isLet then continue
                if ← Lean.Meta.isProp d.type then
                  let ty := (← Lean.instantiateMVars d.type).consumeMData
                  let head? := ty.getAppFn.constName?
                  let badNot := head? == some ``Not && ty.getAppNumArgs ≥ 1 &&
                    let inner := (ty.getArg! 0).consumeMData.getAppFn.constName?
                    inner != some ``LT.lt && inner != some ``LE.le
                  let badRecEq := head? == some ``Eq && ty.getAppNumArgs ≥ 3 &&
                    let ety := (ty.getArg! 0).consumeMData
                    ety.isAppOf ``FullScratch || ety.isAppOf ``FullCoreState ||
                      ety.isAppOf ``FullState || ety.isAppOf ``List || ety.isAppOf ``ExtHashMap
                  let badGet := !usesGetElem && hasGetElem ty
                  let isBig := ty.isForall && !ty.bindingBody!.consumeMData.isConstOf ``False
                  if isBig || badNot || badRecEq || badGet ||
                      (head?.any (clearSet.contains ·)) then
                    ids := ids.push d.fvarId
              pure ids
            let g' ← g'.tryClearMany toClear
            setGoals [g']
            evalTactic (← `(tactic|
              ((try simp only [fc_getElem_vals, fc_getElem_flags, fc_getElem_lvl, fc_getElem_rsns,
                 fc_getElem_trl, fc_getElem_trail_pos, fc_getElem_wvec, fc_getElem_arena,
                 fc_getElem_wstk, fc_getElem_phases, fastPropMem_vals, fastPropMem_flags,
                 fastPropMem_lvl, fastPropMem_rsns, fastPropMem_trl, fastPropMem_trail_pos,
                 fastPropMem_wvec, fastPropMem_arena, fastPropMem_wstk, fastPropMem_phases,
                 fastPropMem_cur_vars, fastPropMem_cur_level, fastPropMem_arena_len,
                 fastPropMem_oom, fastPropMem_wlen, fastPropMem_wusable, fastPropMem_probing,
                 fastPropMem_propagated, fastPropMem_trail_end, fastPropMem_unassigned,
                 fastPropMem_unflushed, fastPropMem_search_ticks, bv_c0_zext32_64,
                 ← BitVec.ofNat_eq_ofNat] at *)
               (try dsimp (config := { zeta := false }) only)
               (try simp only [List.length_set, bv_c0_zext32_64, bv32_xor_1, bv32_lshr_1,
                 fc_bv64_shl1_u32_nat, fc_bv64_shl1_add1_nat]))))
            let g' ← getMainGoal
            let gTy2 ← Lean.instantiateMVars (← g'.getType)
            if (gTy2.find? (·.isConstOf ``List.length)).isSome then
              let eqHyps ← g'.withContext do
                let mut ids : Array Lean.FVarId := #[]
                for d in (← Lean.getLCtx).decls do
                  let some d := d | continue
                  if d.isAuxDecl || d.isLet then continue
                  let ty := (← Lean.instantiateMVars d.type).consumeMData
                  if ty.isAppOf ``Eq && ty.getAppNumArgs ≥ 3 &&
                      ((ty.getArg! 1).find? (·.isConstOf ``List.length)).isSome then
                    ids := ids.push d.fvarId
                pure ids
              for fid in eqHyps do
                let gCur ← getMainGoal
                let curTy ← Lean.instantiateMVars (← gCur.getType)
                if !(curTy.find? (·.isConstOf ``List.length)).isSome then break
                let sEq ← saveState
                try
                  let res : Lean.Meta.RewriteResult ← gCur.withContext <|
                    gCur.rewrite curTy (Lean.mkFVar fid)
                  if res.mvarIds.isEmpty then
                    let gNext ← gCur.replaceTargetEq res.eNew res.eqProof
                    setGoals [gNext]
                  else sEq.restore
                catch _ => sEq.restore
            let g' ← getMainGoal
            let gTy3 ← Lean.instantiateMVars (← g'.getType)
            let hasLen (e : Lean.Expr) : Bool := (e.find? (·.isConstOf ``List.length)).isSome
            let rhsHasLen : Bool :=
              if (gTy3.isAppOf ``LT.lt || gTy3.isAppOf ``LE.le) && gTy3.getAppNumArgs ≥ 4 then
                hasLen (gTy3.getArg! 3)
              else hasLen gTy3
            let g' ← getMainGoal
            let gTy4 ← Lean.instantiateMVars (← g'.getType)
            let hasFpm (e : Lean.Expr) : Bool := (e.find? (·.isConstOf ``fastPropMem)).isSome
            let rhsHasFpm : Bool :=
              if (gTy4.isAppOf ``LT.lt || gTy4.isAppOf ``LE.le) && gTy4.getAppNumArgs ≥ 4 then
                hasFpm (gTy4.getArg! 3)
              else hasFpm gTy4
            let clearLen := !rhsHasLen
            let clearFpm := !rhsHasFpm
            let toClear2 ← g'.withContext do
              let mut ids : Array Lean.FVarId := #[]
              for d in (← Lean.getLCtx).decls do
                let some d := d | continue
                if d.isAuxDecl || d.isLet then continue
                let dTy ← Lean.instantiateMVars d.type
                if (clearLen && !hasGetElem dTy && hasLen dTy) || (clearFpm && hasFpm dTy) ||
                    (d.userName.toString.startsWith "hlen" && clearLen) then
                  ids := ids.push d.fvarId
              pure ids
            let g' ← g'.tryClearMany toClear2
            setGoals [g']
            evalTactic (← `(tactic|
              (first | assumption | rfl | decide
                     | omega
                     | ((try simp only [BitVec.toNat_add, BitVec.ofNat_eq_ofNat,
                           bv_c0_zext32_64, fc_bv64_ofNat_toNat, fc_bv32_ofNat_toNat,
                           BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, BitVec.reduceToNat])
                        (try simp only [fc_nat_xor_one] at *); try omega))))
            if !(← getUnsolvedGoals).isEmpty then
              allOk := false
        for g' in sub do
          if !(← g'.isAssigned) then
            allOk := false
        pure allOk
      catch _ =>
        pure false
      if ok then solved := true; break
      else s.restore
    if !solved then throwError "fc_head_steps: solveMem failed on {← hmv.getType}"
  let headBetaWp (g : Lean.MVarId) : TacticM Lean.MVarId :=
    g.withContext do
      let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData.headBeta
      if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 then
        let e' := (ty.getArg! 4).consumeMData.headBeta.consumeMData
        if e' == ty.getArg! 4 then return g
        let mvar ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar
          (Lean.mkAppN ty.getAppFn (ty.getAppArgs.set! 4 e'))
        g.assign (← Lean.Meta.mkAppM ``fc_wp_head_eq #[← Lean.Meta.mkEqRefl e', mvar])
        return mvar.mvarId!
      return g
  let mut todo ← getGoals
  let mut done : List Lean.MVarId := []
  while !todo.isEmpty do
    let g0 :: rest := todo | break
    todo := rest
    let g ← headBetaWp g0
    let head? ← g.withContext do
      let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData
      if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 then
        return some ((ty.getArg! 4).consumeMData.getAppFn.constName?, ty.getArg! 5)
      return none
    let some (fn?, m0) := head? | done := g :: done; continue
    if fn? == some ``LeanQbe.T.Blocks.get then
      setGoals [g]
      evalTactic (← `(tactic| apply fc_wp_blocks_here))
      todo := (← getGoals) ++ todo
    else if fn? == some ``LeanQbe.T.Expr.let_ then
      let fastGoal? ← g.withContext do
        let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData
        let e := (ty.getArg! 4).consumeMData
        if e.getAppNumArgs < 6 then return none
        let op := (e.getArg! 4).consumeMData
        if !(op.isAppOf ``LeanQbe.T.Op.mk && op.getAppNumArgs ≥ 5) then return none
        let gΓ := ty.getArg! 0; let grs := ty.getArg! 1; let gQ := ty.getArg! 2
        let gX := ty.getArg! 3; let gm := ty.getArg! 5; let gk := e.getArg! 5
        let code := (op.getArg! 3).consumeMData; let args := (op.getArg! 4).consumeMData
        let applyPf (nm : Lean.Name) (xs : Array (Option Lean.Expr)) :
            Lean.Meta.MetaM (Option Lean.MVarId) := do
          let s ← saveState
          try
            let [hk] ← Lean.Meta.withReducible <| g.apply (← Lean.Meta.mkAppOptM nm xs) |
              s.restore; return none
            return some hk
          catch _ => s.restore; return none
        let c := code.getAppFn.constName?
        let key? :=
          if c == some ``OpCode.cmp && code.getAppNumArgs ≥ 1 then
            (code.getArg! 0).consumeMData.getAppFn.constName?
          else c
        if !(args.isAppOf ``Prod.mk && args.getAppNumArgs ≥ 4) then return none
        let a := args.getArg! 2; let r := (args.getArg! 3).consumeMData
        let some (va, ia) := argVal a | return none
        if let some (_, nm) := key?.bind fun k => binOps.find? (·.1 == k) then
          if !(r.isAppOf ``Prod.mk && r.getAppNumArgs ≥ 4) then return none
          let b := r.getArg! 2
          let some (vb, ib) := argVal b | return none
          if ia && ib then return none
          applyPf nm #[some gΓ, some grs, none, some gQ, some gX, some gm, some a, some b,
            some va, some vb, some gk, some (← Lean.Meta.mkEqRefl va),
            some (← Lean.Meta.mkEqRefl vb)]
        else if let some (_, nm) := c.bind fun k => unOps.find? (·.1 == k) then
          if ia then return none
          applyPf nm #[some gΓ, some grs, some gQ, some gX, some gm, some a, some va, some gk,
            some (← Lean.Meta.mkEqRefl va)]
        else if c == some ``OpCode.shl && !ia && r.isAppOf ``Prod.mk &&
            r.getAppNumArgs ≥ 4 then
          let b := r.getArg! 2
          let some (vb, _) := argVal b | return none
          applyPf ``fc_let_shl64_1 #[some gΓ, some grs, some gQ, some gX, some gm, some a, some b,
            some va, some gk, some (← Lean.Meta.mkEqRefl va), some (← Lean.Meta.mkEqRefl vb)]
        else if c == some ``OpCode.lshr && !ia && r.isAppOf ``Prod.mk &&
            r.getAppNumArgs ≥ 4 then
          let b := r.getArg! 2
          let some (vb, _) := argVal b | return none
          applyPf ``fc_let_lshr32_1 #[some gΓ, some grs, some gQ, some gX, some gm, some a, some b,
            some va, some gk, some (← Lean.Meta.mkEqRefl va), some (← Lean.Meta.mkEqRefl vb)]
        else return none
      if let some hk := fastGoal? then
        todo := hk :: todo
      else
        setGoals [g]
        evalTactic (← `(tactic| (
          apply fc_wp_let_head
          · intro P hP; try dsimp (config := { zeta := false }) only
            simp only [OpCode.wp, OpCode.wp_cmp, OpCode.wp_select, OpCode.eq, OpCode.ne,
              OpCode.ult, OpCode.ule, OpCode.ugt, OpCode.uge, OpCode.slt, OpCode.sle, OpCode.sgt,
              OpCode.sge, vals_nil, vals_cons, Arg.val_var, Arg.val_imm, Ty.hasFloat_vec,
              Ty.hasFloat, Ty.isFloatTree, evalBits_eq_beq, evalBits_ne_bne, evalBits_ult_eq,
              evalBits_ule_eq, evalBits_ugt_eq, evalBits_uge_eq, evalBits_slt_eq,
              evalBits_sle_eq, evalBits_sgt_eq, evalBits_sge_eq, evalBool_eq_beq,
              evalBool_ne_bne, evalBool_ult_eq, evalBool_ule_eq, evalBool_ugt_eq,
              evalBool_uge_eq, evalBool_slt_eq, evalBool_sle_eq, evalBool_sgt_eq,
              evalBool_sge_eq, lift1, lift2, lift3, liftCmp, cast_eq, ite_true, ite_false,
              Bool.false_eq_true, Bool.true_eq_false, BitVec.reduceSignExtend,
              BitVec.reduceSetWidth, BitVec.reduceAdd, BitVec.reduceMul, BitVec.reduceToNat,
              Nat.reduceMod, Nat.reduceDiv]
            try refine ⟨by decide, ?_⟩
            exact hP)))
        todo := (← getGoals) ++ todo
    else if fn? == some ``LeanQbe.T.Expr.load then
      let gs ← g.withContext <| Lean.Meta.withReducible <|
        g.apply (← Lean.Meta.mkConstWithFreshMVarLevels ``LeanQbe.T.wp_load_of)
      let [hl, hk] := gs.take 2 | throwError "fc_head_steps: bad load"
      solveMem true hl
      todo := hk :: todo
    else if fn? == some ``LeanQbe.T.Expr.store then
      let gs ← g.withContext <| Lean.Meta.withReducible <|
        g.apply (← Lean.Meta.mkConstWithFreshMVarLevels ``LeanQbe.T.wp_store_sep)
      let [hs, hk] := gs.take 2 | throwError "fc_head_steps: bad store"
      solveMem false hs
      setGoals [hk]
      let mId := Lean.mkIdent `m
      let hmId := Lean.mkIdent `hm
      evalTactic (← `(tactic| intro $mId:ident $hmId:ident))
      evalTactic (← `(tactic| try simp only [LeanQbe.T.Arg.val_var,
        LeanQbe.T.Arg.val_imm, Std.ExtHashMap.sep_emp] at $hmId:ident))
      evalTactic (← `(tactic| try dsimp (config := { zeta := false }) only at $hmId:ident))
      if let .fvar mId0 := m0 then
        withMainContext do
          for d in (← Lean.getLCtx).decls.toArray.reverse do
            let some d := d | continue
            let t ← Lean.instantiateMVars d.type
            if t.isAppOf ``Std.ExtHashMap.sep && t.appArg! == m0 then
              try liftMetaTactic1 fun g => some <$> g.clear d.fvarId catch _ => pure ()
          try liftMetaTactic1 fun g => some <$> g.clear mId0 catch _ => pure ()
      todo := (← getGoals) ++ todo
    else if fn? == some ``LeanQbe.T.Expr.jnz then
      setGoals [g]
      let hc := Lean.mkIdent `hc
      evalTactic (← `(tactic|
        refine wp_jnz_of (fun $hc:ident => ?_) (fun $hc:ident => ?_) <;> (
          try simp only [Arg.val_var, Arg.val_imm] at $hc:ident
          c0_cond $hc
          try (with_reducible
            first | exact ($hc).elim | exact absurd rfl $hc | exact $hc rfl
                  | exact absurd trivial $hc))))
      if stopAtJnz then
        done := (← getGoals).reverse ++ done
      else
        todo := (← getGoals) ++ todo
    else if fn? == some ``LeanQbe.T.Expr.ret then
      setGoals [g]
      evalTactic (← `(tactic|
        (apply fc_wp_ret_head; simp only [vals_nil, vals_cons, Arg.val_var, Arg.val_imm])))
      done := (← getGoals).reverse ++ done
    else if fn? == some ``LeanQbe.T.Expr.jump then
      setGoals [g]
      evalTactic (← `(tactic|
        (apply fc_wp_jump_head; simp only [vals_nil, vals_cons, Arg.val_var, Arg.val_imm])))
      done := (← getGoals).reverse ++ done
    else
      done := g :: done
  setGoals done.reverse

local elab "fc_head_steps" : tactic => do
  Lean.Elab.Tactic.evalTactic
    (← `(tactic| try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)))
  fcHeadRun false

local elab "fc_head_split" : tactic => do
  Lean.Elab.Tactic.evalTactic
    (← `(tactic| try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)))
  fcHeadRun true

theorem fastPropMem_lengthsOk {c : FullCfg} {s0 sem mem : FullState}
    (hlen0 : s0.LengthsOk c) (hlen : sem.LengthsOk c)
    (hcur : sem.core.cur_vars = s0.core.cur_vars) (hpr : sem.core.propagated = s0.core.propagated)
    (hmem : mem = fastPropMem s0 sem) : mem.LengthsOk c := by
  subst hmem
  rw [fastPropMem_def]
  exact
    ⟨{ hlen.core_ok with
        trail_end_le := by dsimp only; rw [hcur]; exact hlen0.core_ok.trail_end_le
        propagated_le := by dsimp only; rw [hpr]; exact hlen0.core_ok.propagated_le },
     hlen.scratch_ok.with_ticks _⟩

theorem fastPropMem_watchLayout {s0 sem mem : FullState}
    (hlay : WatchStackLayout sem.core) (hmem : mem = fastPropMem s0 sem) :
    WatchStackLayout mem.core := by
  subst hmem
  rw [fastPropMem_def]
  exact { bounds := hlay.bounds, pos_off := hlay.pos_off, disjoint := hlay.disjoint,
          no_sentinel := hlay.no_sentinel }

theorem fastTrailExt_congr {k0 k1 k2 : FullCoreState} (h : FullTrailExt k0 k1)
    (hte : k2.trail_end = k1.trail_end) (htrl : k2.trl = k1.trl) (hlvl : k2.lvl = k1.lvl) :
    FullTrailExt k0 k2 :=
  ⟨hte.symm ▸ h.1, fun i hi => htrl ▸ h.2.1 i hi, fun i hi => hlvl ▸ h.2.2 i hi⟩

theorem fastTrailExt_trans {k1 k2 k3 : FullCoreState}
    (h1 : FullTrailExt k1 k2) (h2 : FullTrailExt k2 k3) : FullTrailExt k1 k3 :=
  ⟨Nat.le_trans h1.1 h2.1,
   fun i hi => (h2.2.1 i (by have := h1.1; omega)).trans (h1.2.1 i hi),
   fun i hi => by
     have h2l := h2.2.2 i (by have := h1.1; omega)
     rw [h1.2.1 i hi] at h2l; exact h2l.trans (h1.2.2 i hi)⟩

theorem fastArenaPerm_trans {k1 k2 k3 : FullCoreState}
    (h1 : FullArenaPermEq k1 k2) (h2 : FullArenaPermEq k2 k3) : FullArenaPermEq k1 k3 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, fun r hr =>
    let ⟨s1, g1, p1⟩ := h1.2.2 r hr
    let ⟨s2, g2, p2⟩ := h2.2.2 r (h1.2.1.symm ▸ hr)
    ⟨s2.trans s1, g2.trans g1, p2.trans p1⟩⟩

theorem fullConflOkW_to_fullConflictOkW {F_cur : List (List Nat)} {s : FullState}
    (h : FullConflOkW F_cur s.core) : FullConflictOkW F_cur s := by
  rcases h with ⟨ht, h0, h1, he, hv0, hv1⟩ | ⟨ht, hr, hg, hl⟩
  · exact Or.inl ⟨ht, h0, h1, hv0, hv1, he⟩
  · exact Or.inr ⟨ht, hr, hg, hl⟩

theorem fastProp_nlLvl_const {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} {not_lit other : BitVec 32} {alvl : BitVec 32}
    (hnw : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k))
    (hnot_lt : not_lit.toNat < 2 * k.cur_vars) (hnot_f : k.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8)
    (hother_lt : other.toNat < 2 * k.cur_vars) (hun : k.vals[other.toNat]?.getD 0#8 = 0#8) :
    other.toNat / 2 ≠ not_lit.toNat / 2 ∧
    (k.lvl.set (other.toNat / 2) alvl)[not_lit.toNat / 2]?.getD 0#32 =
      k.lvl[not_lit.toNat / 2]?.getD 0#32 ∧
    (k.lvl[not_lit.toNat / 2]?.getD 0#32).toNat ≤ k.cur_level := by
  obtain ⟨i, hi, heq⟩ := (hnw.vals_false_iff not_lit.toNat hnot_lt).mp hnot_f
  have hnv := (hnw.vals_zero_iff hother_lt).mp hun i hi
  have hvar : (k.trl[i]?.getD 0#32).toNat / 2 = not_lit.toNat / 2 := by
    rw [heq]; exact fullInv_var_xor1 not_lit.toNat
  have hne : other.toNat / 2 ≠ not_lit.toNat / 2 := fun h => hnv (by rw [hvar, h])
  have hle : (k.lvl[not_lit.toNat / 2]?.getD 0#32).toNat ≤ k.cur_level := by
    have := hnw.lvl_le i hi; rwa [hvar] at this
  exact ⟨hne, by rw [List.getElem?_set_ne hne], hle⟩

theorem fastPropMem_eq_of_eq {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sem : FullState} {not_lit : BitVec 32} {off_v q0 p0 q_v p_v end_v : Nat}
    {wstk' flags' : List (BitVec 32)} {ph' : List (BitVec 8)}
    {other alvl rsn nl_lvl0 : BitVec 32} {unas' unfl' : BitVec 64}
    (hpi : PropLitInv c F0 F_cur s sem not_lit.toNat off_v q0 p0 end_v)
    (hsw1 : SplitWatchesInv F_cur { sem.core with wstk := wstk' } not_lit.toNat off_v q_v p_v end_v)
    (hws_len : wstk'.length = c.wcap)
    (hfl_len : flags'.length = c.max_vars) (hph_len : ph'.length = c.max_vars)
    (hnot_lt : not_lit.toNat < 2 * sem.core.cur_vars)
    (hother_lt : other.toNat < 2 * sem.core.cur_vars)
    (hun : sem.core.vals[other.toNat]?.getD 0#8 = 0#8)
    (hnl_eq : sem.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0)
    (hassign :
      let sem1core : FullCoreState := { sem.core with wstk := wstk' }
      let k2 : FullCoreState :=
        { sem1core with
          vals := (sem1core.vals.set other.toNat 1#8).set (other.toNat ^^^ 1) 0xFF#8
          flags := flags', lvl := sem1core.lvl.set (other.toNat / 2) alvl
          rsns := sem1core.rsns.set (other.toNat / 2)
            (if alvl = 0#32 then 0xFFFFFFFF#32 else rsn)
          trl := sem1core.trl.set sem1core.trail_end other
          trail_pos := sem1core.trail_pos.set (other.toNat / 2)
            (BitVec.ofNat 32 sem1core.trail_end)
          trail_end := sem1core.trail_end + 1
          unassigned := unas', unflushed := unfl' }
      FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k2) ∧
      k2.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8 ∧
      FullPropDecSpecs.FullTrailExt sem1core k2) :
    let sem1core : FullCoreState := { sem.core with wstk := wstk' }
    let sem2 : FullState :=
      { core :=
          { sem1core with
            vals := (sem1core.vals.set other.toNat 1#8).set (other.toNat ^^^ 1) 0xFF#8
            flags := flags', lvl := sem1core.lvl.set (other.toNat / 2) alvl
            rsns := sem1core.rsns.set (other.toNat / 2)
              (if alvl = 0#32 then 0xFFFFFFFF#32 else rsn)
            trl := sem1core.trl.set sem1core.trail_end other
            trail_pos := sem1core.trail_pos.set (other.toNat / 2)
              (BitVec.ofNat 32 sem1core.trail_end)
            trail_end := sem1core.trail_end + 1
            unassigned := unas', unflushed := unfl' }
        scratch := { sem.scratch with phases := ph' } }
    sem2.LengthsOk c ∧ FullWitnessInv c F0 F_cur (withEmptyWatchesCore c sem2.core) ∧
    SplitWatchesInv F_cur sem2.core not_lit.toNat off_v q_v p_v end_v ∧
    AgreesExcept propLitCoreMask s.core sem2.core ∧
    FullPropDecSpecs.FullTrailExt s.core sem2.core ∧
    FullPropDecSpecs.FullArenaPermEq s.core sem2.core ∧
    sem2.scratch = { s.scratch with
      search_ticks := sem2.scratch.search_ticks, wsort := sem2.scratch.wsort,
      phases := sem2.scratch.phases } ∧
    sem2.core.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8 ∧
    sem2.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0 := by
  intro sem1core sem2
  have hcl := hpi.len.core_ok
  have hnw1 : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c sem1core) :=
    fullWitnessInv_nw_congr hcl.cur_vars_le hpi.nw
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hte_lt : sem.core.trail_end < sem.core.cur_vars :=
    hnw1.trail_end_lt_of_unassigned hother_lt hun
  have hlen2 : sem2.LengthsOk c :=
    ⟨{ hcl with
        vals_len := by simp [sem2, sem1core, hcl.vals_len], flags_len := hfl_len,
        lvl_len := by simp [sem2, sem1core, hcl.lvl_len],
        rsns_len := by simp [sem2, sem1core, hcl.rsns_len],
        trl_len := by simp [sem2, sem1core, hcl.trl_len],
        trail_pos_len := by simp [sem2, sem1core, hcl.trail_pos_len],
        wstk_len_arr := hws_len,
        trail_end_le := by dsimp [sem2, sem1core]; omega,
        propagated_le := by have := hcl.propagated_le; dsimp [sem2, sem1core]; omega },
     { hpi.len.scratch_ok with phases_len := hph_len }⟩
  obtain ⟨hnw2, hnot_f2, htr12⟩ := hassign
  have ⟨_, hnl_keep, _⟩ := fastProp_nlLvl_const (alvl := alvl) hnw1 hnot_lt hpi.not_f hother_lt hun
  refine ⟨hlen2, hnw2, hsw1.with_nonwatch rfl rfl rfl rfl rfl,
    hpi.ag.update (fun k => { k with
      vals := sem2.core.vals, flags := flags', lvl := sem2.core.lvl, rsns := sem2.core.rsns,
      trl := sem2.core.trl, trail_pos := sem2.core.trail_pos, trail_end := sem2.core.trail_end,
      unassigned := unas', unflushed := unfl', wstk := wstk' }),
    (hpi.tr.congr (k2 := sem1core) rfl rfl rfl).trans htr12, hpi.perm,
    by dsimp only [sem2]; rw [hpi.sc_eq], hnot_f2, by dsimp [sem2, sem1core]; rw [hnl_keep, hnl_eq]⟩

theorem fastProp_nonchrono_alvl {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} {cref other not_lit nl_lvl : BitVec 32}
    (hnw : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k))
    (hcref : cref.toNat ∈ fullArenaClauseRefsCore k)
    (hng : fullArenaClauseGarbCore k cref.toNat = false)
    (hnot_f : k.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8)
    (hun : k.vals[other.toNat]?.getD 0#8 = 0#8)
    (hnot_mem : not_lit.toNat ∈ fullArenaClauseLitsCore k cref.toNat)
    (hunit : ∀ l ∈ fullArenaClauseLitsCore k cref.toNat,
      l = other.toNat ∨ k.vals[l]?.getD 0#8 = 0xFF#8)
    (hnl_eq : k.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl)
    (hnot_ult : nl_lvl.ult (BitVec.ofNat 32 k.cur_level) = false)
    (hcl32 : k.cur_level < 2 ^ 32) :
    (∀ l ∈ fullArenaClauseLitsCore k cref.toNat, l ≠ other.toNat →
      (k.lvl[l / 2]?.getD 0#32).toNat ≤ nl_lvl.toNat) ∧
    (nl_lvl = 0#32 ∨ ∃ l ∈ fullArenaClauseLitsCore k cref.toNat,
      l ≠ other.toNat ∧ nl_lvl = k.lvl[l / 2]?.getD 0#32) := by
  have hge : k.cur_level ≤ nl_lvl.toNat := by
    rw [BitVec.ult_eq_decide] at hnot_ult
    have := of_decide_eq_false hnot_ult
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl32] at this
    omega
  have hnot_ne : not_lit.toNat ≠ other.toNat := fun heq => by rw [heq, hun] at hnot_f; cases hnot_f
  refine ⟨fun l hl hne => ?_, Or.inr ⟨not_lit.toNat, hnot_mem, hnot_ne, hnl_eq.symm⟩⟩
  have hfl := (hunit l hl).resolve_left hne
  obtain ⟨i, hi, hieq⟩ := (hnw.vals_false_iff l (hnw.arena.lits_lt _ hcref hng l hl)).mp hfl
  have hle : (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ k.cur_level :=
    hnw.lvl_le i hi
  rw [hieq, fullInv_var_xor1 l] at hle
  exact Nat.le_trans hle hge

theorem fastProp_findRepl_ok {st : FullState} {cref r : Nat}
    {hi_lt : cref + 3 + r < st.core.arena.length}
    {hj_lt : (st.core.arena[cref + 3 + r]'hi_lt).toNat < st.core.vals.length}
    (hcv : (st.core.arena[cref + 3 + r]'hi_lt).toNat < 2 * st.core.cur_vars)
    (hsle : (0#32).sle ((st.core.vals[(st.core.arena[cref + 3 + r]'hi_lt).toNat]'hj_lt).signExtend
      32) = true) :
    let cand := (st.core.arena[cref + 3 + r]?.getD 0#32).toNat
    cand < 2 * st.core.cur_vars ∧
    ((st.core.vals[cand]?.getD 0#8).signExtend 32).slt 0#32 = false := by
  dsimp only
  rw [List.getElem?_eq_getElem hi_lt, Option.getD_some,
    List.getElem?_eq_getElem hj_lt, Option.getD_some]
  refine ⟨hcv, ?_⟩; rw [bv32_sle0_eq_not_slt0, Bool.not_eq_true'] at hsle; exact hsle

theorem fastProp_findRepl_bad_slt {st : FullState} {cref r : Nat}
    {hi_lt : cref + 3 + r < st.core.arena.length}
    {hj_lt : (st.core.arena[cref + 3 + r]'hi_lt).toNat < st.core.vals.length}
    (h : (0#32).sle ((st.core.vals[(st.core.arena[cref + 3 + r]'hi_lt).toNat]'hj_lt).signExtend
      32) = false) :
    fullFindReplBad st cref r := by
  unfold fullFindReplBad; refine Or.inr ?_
  rw [List.getElem?_eq_getElem hi_lt, Option.getD_some,
    List.getElem?_eq_getElem hj_lt, Option.getD_some]
  rw [bv32_sle0_eq_not_slt0, Bool.not_eq_false'] at h; exact h

theorem fastProp_findRepl_bad_oob {st : FullState} {cref r : Nat}
    {hi_lt : cref + 3 + r < st.core.arena.length}
    (h : ¬ (st.core.arena[cref + 3 + r]'hi_lt).toNat < 2 * st.core.cur_vars) :
    fullFindReplBad st cref r := by
  unfold fullFindReplBad; refine Or.inl ?_
  rw [List.getElem?_eq_getElem hi_lt, Option.getD_some]; omega

theorem fastProp_lt_vals {k : FullCoreState} {c : FullCfg} {o : Nat}
    (hk : k.LengthsOk c) (ho : o < 2 * k.cur_vars) : o < k.vals.length := by
  rw [hk.vals_len]; exact Nat.lt_of_lt_of_le ho (Nat.mul_le_mul_left 2 hk.cur_vars_le)

theorem fc_rem2_lt {p e : Nat} (h : p + 2 ≤ e) : e - (p + 2) < e - p := by omega

theorem fc_cref_bounds {c : FullCfg} {k : FullCoreState} {cref : BitVec 32}
    (hlen : k.LengthsOk c) (har : c.arena_cap < 2 ^ 32)
    (h3 : 3 ≤ fullArenaClauseSizeCore k cref.toNat)
    (hfit : cref.toNat + 3 + fullArenaClauseSizeCore k cref.toNat ≤ k.arena_len) :
    cref.toNat < k.arena.length ∧ cref.toNat + 2 < k.arena.length ∧
    cref.toNat + 3 < k.arena.length ∧ cref.toNat + 4 < k.arena.length ∧
    cref.toNat + 3 < 2 ^ 64 ∧ k.arena_len < 2 ^ 64 := by
  have halen_le := hlen.arena_len_le; have haren := hlen.arena_len_arr
  have hcr5 : cref.toNat + 5 ≤ k.arena_len := by omega
  have hal64 : k.arena_len < 2 ^ 64 :=
    Nat.lt_of_le_of_lt halen_le (Nat.lt_trans har (by decide))
  refine ⟨?_, ?_, ?_, ?_, by omega, hal64⟩ <;> (rw [haren]; omega)

theorem fastProp_js3_swap {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st_t : FullState} {not_lit cref l1 : BitVec 32} {off_v p_v q_v end_v : BitVec 64}
    (hpi_t : PropLitInv c F0 F_cur s st_t not_lit.toNat off_v.toNat q_v.toNat (p_v.toNat + 2)
      end_v.toNat)
    (hcr_ref : cref.toNat ∈ fullArenaClauseRefsCore st_t.core)
    (hng_t : fullArenaClauseGarbCore st_t.core cref.toNat = false)
    (hcsz3 : 3 ≤ fullArenaClauseSizeCore st_t.core cref.toNat)
    (hcr_fit : cref.toNat + 3 + fullArenaClauseSizeCore st_t.core cref.toNat ≤ st_t.core.arena_len)
    (hl0_eq : st_t.core.arena[cref.toNat + 3]'(by
      have := hpi_t.len.core_ok.arena_len_arr; have := hpi_t.len.core_ok.arena_len_le
      omega) = not_lit)
    (hl1_eq : st_t.core.arena[cref.toNat + 4]'(by
      have := hpi_t.len.core_ok.arena_len_arr; have := hpi_t.len.core_ok.arena_len_le
      omega) = l1) :
    let st1 : FullState := { st_t with core := { st_t.core with
      arena := (st_t.core.arena.set (cref.toNat + 3) l1).set (cref.toNat + 4) not_lit } }
    PropLitInv c F0 F_cur s st1 not_lit.toNat off_v.toNat q_v.toNat (p_v.toNat + 2) end_v.toNat ∧
    cref.toNat ∈ fullArenaClauseRefsCore st1.core ∧
    fullArenaClauseGarbCore st1.core cref.toNat = false ∧
    fullArenaClauseSizeCore st1.core cref.toNat = fullArenaClauseSizeCore st_t.core cref.toNat ∧
    st1.core.arena[cref.toNat + 3]? = some l1 ∧ st1.core.arena[cref.toNat + 4]? = some not_lit := by
  intro st1
  have haren := hpi_t.len.core_ok.arena_len_arr; have halen := hpi_t.len.core_ok.arena_len_le
  have ⟨hnw1, hperm_t1⟩ := full_swapLits_preserves_nw hpi_t.len.core_ok hpi_t.nw hcr_ref
    (k1 := 0) (k2 := 1) (by omega) (by omega)
  have hst1_sw : st1.core = { st_t.core with
    arena := (st_t.core.arena.set (cref.toNat + 3 + 0)
        (st_t.core.arena[cref.toNat + 3 + 1]'(by omega))).set
      (cref.toNat + 3 + 1) (st_t.core.arena[cref.toNat + 3 + 0]'(by omega)) } := by
    simp only [st1, hl0_eq, hl1_eq]
  rw [← hst1_sw] at hnw1 hperm_t1
  have hlen1 : st1.LengthsOk c :=
    ⟨{ hpi_t.len.core_ok with arena_len_arr := by simp [st1, haren] }, hpi_t.len.scratch_ok⟩
  refine ⟨{ len := hlen1, nw := hnw1
            sw := hpi_t.sw.with_nonwatch (k' := st1.core) rfl rfl rfl rfl hperm_t1.1
            ag := hpi_t.ag.update (fun k => { k with arena := st1.core.arena })
            tr := hpi_t.tr.congr rfl rfl rfl, perm := hpi_t.perm.trans hperm_t1
            sc_eq := hpi_t.sc_eq, not_f := hpi_t.not_f },
    hperm_t1.1.symm ▸ hcr_ref, (hperm_t1.2 cref.toNat hcr_ref).2.1.trans hng_t,
    (hperm_t1.2 cref.toNat hcr_ref).1,
    by simp [st1, List.getElem?_set_ne (by omega : cref.toNat + 4 ≠ cref.toNat + 3),
         List.getElem?_set_self (show cref.toNat + 3 < st_t.core.arena.length by omega)],
    by rw [List.getElem?_set_self (by simp; omega)]⟩

theorem fastProp_b1_swap {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st1 : FullState} {not_lit other cref repl : BitVec 32} {off_v p_v q_v end_v : BitVec 64}
    {r : Nat}
    (hpi1 : PropLitInv c F0 F_cur s st1 not_lit.toNat off_v.toNat q_v.toNat (p_v.toNat + 2)
      end_v.toNat)
    (hcr_lt : cref.toNat < st1.core.arena_len)
    (hcr_ref1 : cref.toNat ∈ fullArenaClauseRefsCore st1.core)
    (hcr_fit : cref.toNat + 3 + fullArenaClauseSizeCore st1.core cref.toNat ≤ st1.core.arena_len)
    (har4 : st1.core.arena[cref.toNat + 4]? = some not_lit)
    (hr2 : 2 ≤ r) (hr_lt : r < fullArenaClauseSizeCore st1.core cref.toNat)
    (hrepl_def : repl = (st1.core.arena.set (cref.toNat + 1) (BitVec.ofNat 32 r))[cref.toNat + 3 +
      r]'(by
      have := hpi1.len.core_ok.arena_len_arr; have := hpi1.len.core_ok.arena_len_le
      simp; omega))
    (hcand : (st1.core.arena[cref.toNat + 3 + r]?.getD 0#32).toNat < 2 * st1.core.cur_vars ∧
      ((st1.core.vals[(st1.core.arena[cref.toNat + 3 + r]?.getD 0#32).toNat]?.getD 0#8).signExtend
        32).slt 0#32 = false) :
    let st3 : FullState := { st1 with core := { st1.core with
      arena := ((st1.core.arena.set (cref.toNat + 1)
        (BitVec.ofNat 32 r)).set (cref.toNat + 4) repl).set (cref.toNat + 3 + r) not_lit } }
    st3.LengthsOk c ∧ FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st3.core) ∧
    SplitWatchesInv F_cur st3.core not_lit.toNat off_v.toNat q_v.toNat (p_v.toNat + 2)
      end_v.toNat ∧
    FullPropDecSpecs.FullArenaPermEq st1.core st3.core ∧
    cref.toNat ∈ fullArenaClauseRefsCore st3.core ∧
    fullArenaClauseSizeCore st3.core cref.toNat = fullArenaClauseSizeCore st1.core cref.toNat ∧
    repl.toNat < 2 * st1.core.cur_vars ∧ repl.toNat ≠ not_lit.toNat ∧
    (other &&& 0x7FFFFFFF#32) ≠ 0xFFFFFFFF#32 ∧ cref ≠ 0xFFFFFFFF#32 := by
  intro st3
  let st2 : FullState := { st1 with core := { st1.core with
    arena := st1.core.arena.set (cref.toNat + 1) (BitVec.ofNat 32 r) } }
  have har := c.harena; unfold dimacsBound at har
  have haren1 := hpi1.len.core_ok.arena_len_arr; have halen1_le := hpi1.len.core_ok.arena_len_le
  have ⟨hnw2, hperm12⟩ :=
    full_setSrch_preserves_nw hpi1.len.core_ok hpi1.nw hcr_ref1 (srch := BitVec.ofNat 32 r)
  have hlen2 : st2.LengthsOk c :=
    ⟨{ hpi1.len.core_ok with arena_len_arr := by simp [st2, haren1] }, hpi1.len.scratch_ok⟩
  have hsw2 := hpi1.sw.with_nonwatch (k' := st2.core) rfl rfl rfl rfl hperm12.1
  have hcr_ref2 : cref.toNat ∈ fullArenaClauseRefsCore st2.core := hperm12.1.symm ▸ hcr_ref1
  have hcsz2 : fullArenaClauseSizeCore st2.core cref.toNat =
      fullArenaClauseSizeCore st1.core cref.toNat := (hperm12.2 cref.toNat hcr_ref1).1
  have hrepl_get : st1.core.arena[cref.toNat + 3 + r]?.getD 0#32 = repl := by
    have h1 : st2.core.arena[cref.toNat + 3 + r]? = some repl := by
      rw [hrepl_def]; exact List.getElem?_eq_getElem (by simp [st2]; omega)
    rw [← List.getElem?_set_ne (by omega : cref.toNat + 1 ≠ cref.toNat + 3 + r),
      show (st1.core.arena.set (cref.toNat + 1) (BitVec.ofNat 32 r))[cref.toNat + 3 + r]? =
        some repl from h1, Option.getD_some]
  obtain ⟨hrepl_lt, hrepl_slt⟩ := hcand; rw [hrepl_get] at hrepl_lt hrepl_slt
  have hrepl_ne_not : repl.toNat ≠ not_lit.toNat := fun heq =>
    i8_vals_ne_of_slt_false hpi1.not_f (heq ▸ hrepl_slt) rfl
  have hst2_ar4 : st2.core.arena[cref.toNat + 3 + 1]'(by simp [st2]; omega) = not_lit :=
    Option.some.inj ((List.getElem?_eq_getElem (by simp [st2]; omega)).symm.trans
      ((List.getElem?_set_ne (by omega)).trans har4))
  have ⟨hnw3, hperm23⟩ := full_swapLits_preserves_nw hlen2.core_ok hnw2 hcr_ref2 (k1 := 1)
    (k2 := r) (by change 1 < fullArenaClauseSizeCore st2.core cref.toNat; omega)
    (by change r < fullArenaClauseSizeCore st2.core cref.toNat; omega)
  have hst3_sw : st3.core = { st2.core with
    arena := (st2.core.arena.set (cref.toNat + 3 + 1)
        (st2.core.arena[cref.toNat + 3 + r]'(by simp [st2]; omega))).set
      (cref.toNat + 3 + r) (st2.core.arena[cref.toNat + 3 + 1]'(by simp [st2]; omega)) } := by
    simp only [st3, st2, hst2_ar4, ← hrepl_def]
  rw [← hst3_sw] at hnw3 hperm23
  have hw0_ne_ff : (other &&& 0x7FFFFFFF#32) ≠ 0xFFFFFFFF#32 := fun hff => by
    have h := bv32_mask7f_flag0 other; rw [hff] at h; exact absurd h (by decide)
  have hcr_ne_ff : cref ≠ 0xFFFFFFFF#32 := fun hff => by
    rw [hff] at hcr_lt; have : (0xFFFFFFFF#32).toNat = 0xFFFFFFFF := (by decide); omega
  exact ⟨⟨{ hlen2.core_ok with arena_len_arr := by simp [st3, haren1] }, hpi1.len.scratch_ok⟩,
    hnw3, hsw2.with_nonwatch (k' := st3.core) rfl rfl rfl rfl hperm23.1,
    hperm12.trans hperm23, hperm23.1.symm ▸ hcr_ref2,
    (hperm23.2 cref.toNat hcr_ref2).1.trans hcsz2, hrepl_lt, hrepl_ne_not, hw0_ne_ff, hcr_ne_ff⟩

theorem fastProp_b1_oom {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st1 st4 : FullState} {not_lit w0 cref repl : BitVec 32}
    {off_v p_v q_v end_v off4_v : BitVec 64} {r : Nat}
    (hpi1 : PropLitInv c F0 F_cur s st1 not_lit.toNat off_v.toNat q_v.toNat (p_v.toNat + 2)
      end_v.toNat)
    (hlen4 : st4.LengthsOk c) (hnw4 : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st4.core))
    (hsw4' : SplitWatchesInv F_cur st4.core not_lit.toNat off4_v.toNat
      (off4_v + (q_v - off_v)).toNat
      (off4_v + (p_v + (1 : BitVec 64) + (1 : BitVec 64) - off_v)).toNat
      (off4_v + (end_v - off_v)).toNat)
    (hperm4 : FullPropDecSpecs.FullArenaPermEq s.core st4.core)
    (har_eq : st4.core.arena = ((st1.core.arena.set (cref.toNat + 1) (BitVec.ofNat 32 r)).set
      (cref.toNat + 4) repl).set (cref.toNat + 3 + r) not_lit)
    (hal_eq : st4.core.arena_len = st1.core.arena_len)
    (hag4 : AgreesExcept propLitCoreMask s.core st4.core)
    (htr4 : FullPropDecSpecs.FullTrailExt s.core st4.core)
    (hsc4 : st4.scratch = { s.scratch with
      search_ticks := st4.scratch.search_ticks, wsort := st4.scratch.wsort,
      phases := st4.scratch.phases })
    (hnot4 : st4.core.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8)
    (hnot_lt : not_lit.toNat < 2 * st4.core.cur_vars) (hq_le_p : q_v.toNat ≤ p_v.toNat)
    (hcr_lt : cref.toNat < 0x80000000) (hcr_ref3 : cref.toNat ∈ fullArenaClauseRefsCore st4.core)
    (hflag : (w0 &&& 0x80000000#32) = 0#32)
    (hcr_fit : cref.toNat + 3 + fullArenaClauseSizeCore st4.core cref.toNat ≤ st1.core.arena_len)
    (hr2 : 2 ≤ r) (hr_lt : r < fullArenaClauseSizeCore st4.core cref.toNat)
    (hq4_nat : (off4_v + (q_v - off_v)).toNat =
      fullWatchOffCore st4.core not_lit.toNat + (q_v.toNat - off_v.toNat))
    (hp4_nat : (off4_v + (p_v + (1 : BitVec 64) + (1 : BitVec 64) - off_v)).toNat =
      fullWatchOffCore st4.core not_lit.toNat + (p_v.toNat + 2 - off_v.toNat))
    (hq4_2 : (off4_v + (q_v - off_v) + (2 : BitVec 64)).toNat =
      (off4_v + (q_v - off_v)).toNat + 2) :
    let q4_v := off4_v + (q_v - off_v)
    let st6 : FullState := { st4 with core := { st4.core with
      arena := (st4.core.arena.set (cref.toNat + 4) not_lit).set (cref.toNat + 3 + r) repl,
      wstk := (st4.core.wstk.set q4_v.toNat w0).set (q4_v.toNat + 1) cref, oom := 1#64 } }
    PropLitInv c F0 F_cur s st6 not_lit.toNat off4_v.toNat (q4_v + (2 : BitVec 64)).toNat
      (off4_v + (p_v + (1 : BitVec 64) + (1 : BitVec 64) - off_v)).toNat
      (off4_v + (end_v - off_v)).toNat := by
  intro q4_v st6
  have haren4 := hlen4.core_ok.arena_len_arr; have halen4 := hlen4.core_ok.arena_len_le
  have hwstk4 := hlen4.core_ok.wstk_len_arr; have hwlen4 := hlen4.core_ok.wlen_le
  have hb4 := hsw4'.layout.bounds not_lit.toNat hnot_lt
  have hoff4 := hsw4'.off_eq; have hsz4 := hsw4'.sz_eq
  have hq4_ge := hsw4'.q_ge; have hq4_le := hsw4'.q_le_p; have hp4_le := hsw4'.p_le_end
  have hq_ge := hpi1.sw.q_ge; have hq_le := hpi1.sw.q_le_p; have hp_le := hpi1.sw.p_le_end
  have hst4_ar4 : st4.core.arena[cref.toNat + 3 + 1]'(by omega) = repl := by
    have h1 : st4.core.arena[cref.toNat + 4]'(by omega) = repl := by
      simp only [har_eq]; rw [List.getElem_set_ne (by omega), List.getElem_set_self]
    exact h1
  have hst4_arr : st4.core.arena[cref.toNat + 3 + r]'(by omega) = not_lit := by
    simp only [har_eq]; rw [List.getElem_set_self]
  have ⟨hnw5, hperm45⟩ := full_swapLits_preserves_nw hlen4.core_ok hnw4 hcr_ref3 (k1 := 1)
    (k2 := r) (by omega) (by omega)
  let st5 : FullState := { st4 with core := { st4.core with
    arena := (st4.core.arena.set (cref.toNat + 4) not_lit).set (cref.toNat + 3 + r) repl } }
  have hst5_sw : st5.core = { st4.core with
    arena := (st4.core.arena.set (cref.toNat + 3 + 1)
        (st4.core.arena[cref.toNat + 3 + r]'(by omega))).set
      (cref.toNat + 3 + r) (st4.core.arena[cref.toNat + 3 + 1]'(by omega)) } := by
    simp only [st5, hst4_ar4, hst4_arr]
  rw [← hst5_sw] at hnw5 hperm45
  have hcr_ref5 : cref.toNat ∈ fullArenaClauseRefsCore st5.core := hperm45.1.symm ▸ hcr_ref3
  have hsw5 := hsw4'.with_nonwatch (k' := st5.core) rfl rfl rfl rfl hperm45.1
  have hq4_e : q4_v.toNat =
      fullWatchOffCore st4.core not_lit.toNat + (q_v.toNat - off_v.toNat) := hq4_nat
  have hp4_split : (off4_v + (p_v + (1 : BitVec 64) + (1 : BitVec 64) - off_v)).toNat =
      (fullWatchOffCore st4.core not_lit.toNat + (p_v.toNat - off_v.toNat)) + 2 := by omega
  have hsw5_w := (by rwa [hp4_split] at hsw5 :
      SplitWatchesInv F_cur st5.core not_lit.toNat off4_v.toNat q4_v.toNat
        ((fullWatchOffCore st4.core not_lit.toNat + (p_v.toNat - off_v.toNat)) + 2)
        (off4_v + (end_v - off_v)).toNat).write_large hnot_lt (by omega)
    (by simp [st5]; omega) (by simp [st5]; omega) hflag hcr_lt hcr_ref5
  have hlen6 : st6.LengthsOk c :=
    ⟨{ hlen4.core_ok with
        arena_len_arr := by simp [st6, haren4], wstk_len_arr := by simp [st6, hwstk4] },
     hlen4.scratch_ok⟩
  exact
    { len := hlen6
      nw := fullWitnessInv_nw_congr hlen6.core_ok.cur_vars_le hnw5
        rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      sw := by rw [hq4_2, hp4_split]; exact hsw5_w.with_nonwatch rfl rfl rfl rfl rfl
      ag := hag4.update (fun k =>
        { k with arena := st6.core.arena, wstk := st6.core.wstk, oom := 1#64 })
      tr := htr4.congr rfl rfl rfl, perm := hperm4.trans hperm45
      sc_eq := hsc4, not_f := hnot4 }

/-! ## 2. `full_prop_lit`, `full_propagate_ignore`, `full_propagate` -/

def fastPropCoreMask (k : FullCoreState) : FullCoreState :=
  { propLitCoreMask k with propagated := 0, fuel := 0#64 }

def fastPropAssignExpr (other alvl rsn : Val i32) (rec_ph : Val .bool)
    (tend_v unass_v unfl_v max_v vals_p fl_p lvl_p rsns_p tpos_p trl_p ph_p : Val i64)
    (k_next : Val i64 → Val i64 → Val i64 → Expr Val Cont [.bool]) :
    Expr Val Cont [.bool] :=
  .group (sig := [[i64, i64, i64]])
    (fun L2 => .cons (fun p => k_next p.1 p.2.1 p.2.2.1) .nil)
    (fun L2 =>
      .let_ (Op.mk (.cmp .ult i64) (.var tend_v, (.var max_v, ()))) fun c0 =>
      .jnz (.var c0.1) (
        .let_ (Op.mk (.lshr i32) (.var other, (.imm (1 : BitVec 32), ()))) fun ov_v =>
        .let_ (Op.mk (.zext 32 64) (.var other, ())) fun o64 =>
        .let_ (Op.mk (.add i64) (.var vals_p, (.var o64.1, ()))) fun p_v0 =>
        .let_ (Op.mk (.trunc 32 8) (.imm (1 : BitVec 32), ())) fun b1 =>
        .store (.var b1.1) (.var p_v0.1) (
          .let_ (Op.mk (.xor i32) (.var other, (.imm (1 : BitVec 32), ()))) fun no32 =>
          .let_ (Op.mk (.zext 32 64) (.var no32.1, ())) fun no64 =>
          .let_ (Op.mk (.add i64) (.var vals_p, (.var no64.1, ()))) fun p_v1 =>
          .let_ (Op.mk (.neg i32) (.imm (1 : BitVec 32), ())) fun m1 =>
          .let_ (Op.mk (.trunc 32 8) (.var m1.1, ())) fun bm1 =>
          .store (.var bm1.1) (.var p_v1.1) (
            .group (sig := [[i64]])
              (fun L3 => .cons (fun un_n =>
                .group (sig := [[]])
                  (fun L4 => .cons (fun _ =>
                    .let_ (Op.mk (.zext 32 64) (.var ov_v.1, ())) fun v0 =>
                    .let_ (Op.mk (.mul i64) (.var v0.1, (.imm (4 : BitVec 64), ()))) fun v1 =>
                    .let_ (Op.mk (.add i64) (.var lvl_p, (.var v1.1, ()))) fun p_lv =>
                    .store (.var alvl) (.var p_lv.1) (
                      .group (sig := [[i64]])
                        (fun L5 => .cons (fun uf_n =>
                          .let_ (Op.mk (.zext 32 64) (.var ov_v.1, ())) fun z0 =>
                          .let_ (Op.mk (.mul i64) (.var z0.1, (.imm (4 : BitVec 64), ())))
                            fun z1 =>
                          .let_ (Op.mk (.add i64) (.var tpos_p, (.var z1.1, ()))) fun ptp =>
                          .let_ (Op.mk (.trunc 64 32) (.var tend_v, ())) fun te32 =>
                          .store (.var te32.1) (.var ptp.1) (
                            .let_ (Op.mk (.mul i64) (.var tend_v, (.imm (4 : BitVec 64), ())))
                              fun t0 =>
                            .let_ (Op.mk (.add i64) (.var trl_p, (.var t0.1, ()))) fun ptrl =>
                            .store (.var other) (.var ptrl.1) (
                              .let_ (Op.mk (.add i64) (.var tend_v, (.imm (1 : BitVec 64), ())))
                                fun te1 =>
                              .jump L2.1 (.var te1.1, (.var un_n.1, (.var uf_n.1, ())))
                            )
                          )
                        ) .nil)
                        (fun L5 =>
                          .let_ (Op.mk (.cmp .eq i32) (.var alvl, (.imm (0 : BitVec 32), ())))
                            fun c1 =>
                          .jnz (.var c1.1) (
                            .let_ (Op.mk (.zext 32 64) (.var ov_v.1, ())) fun z0 =>
                            .let_ (Op.mk (.mul i64) (.var z0.1, (.imm (4 : BitVec 64), ())))
                              fun z1 =>
                            .let_ (Op.mk (.add i64) (.var rsns_p, (.var z1.1, ()))) fun prs =>
                            .store (t := i32) (.imm (4294967295 : BitVec 32)) (.var prs.1) (
                              .let_ (Op.mk (.zext 32 64) (.var ov_v.1, ())) fun y0 =>
                              .let_ (Op.mk (.mul i64) (.var y0.1, (.imm (4 : BitVec 64), ())))
                                fun y1 =>
                              .let_ (Op.mk (.add i64) (.var fl_p, (.var y1.1, ()))) fun pf0 =>
                              .let_ (Op.mk (.zext 32 64) (.var ov_v.1, ())) fun y2 =>
                              .let_ (Op.mk (.mul i64) (.var y2.1, (.imm (4 : BitVec 64), ())))
                                fun y3 =>
                              .let_ (Op.mk (.add i64) (.var fl_p, (.var y3.1, ()))) fun pf1 =>
                              .load i32 (.var pf1.1) fun fl_v =>
                              .let_ (Op.mk (.not i32) (.imm (1 : BitVec 32), ())) fun nf =>
                              .let_ (Op.mk (.and i32) (.var fl_v, (.var nf.1, ()))) fun fl2 =>
                              .store (.var fl2.1) (.var pf0.1) (
                                .let_ (Op.mk (.add i64) (.var unfl_v, (.imm (1 : BitVec 64), ())))
                                  fun uf1 =>
                                .jump L5.1 (.var uf1.1, ())
                              )
                            )
                          ) (
                            .let_ (Op.mk (.zext 32 64) (.var ov_v.1, ())) fun z0 =>
                            .let_ (Op.mk (.mul i64) (.var z0.1, (.imm (4 : BitVec 64), ())))
                              fun z1 =>
                            .let_ (Op.mk (.add i64) (.var rsns_p, (.var z1.1, ()))) fun prs =>
                            .store (.var rsn) (.var prs.1) (.jump L5.1 (.var unfl_v, ()))
                          )
                        )
                    )
                  ) .nil)
                  (fun L4 =>
                    .jnz (.var rec_ph) (
                      .let_ (Op.mk (.zext 32 64) (.var ov_v.1, ())) fun z0 =>
                      .let_ (Op.mk (.add i64) (.var ph_p, (.var z0.1, ()))) fun pph =>
                      .group (sig := [[i32]])
                        (fun L6 => .cons (fun pv32 =>
                          .let_ (Op.mk (.trunc 32 8) (.var pv32.1, ())) fun pv8 =>
                          .store (.var pv8.1) (.var pph.1) (.jump L4.1 ())
                        ) .nil)
                        (fun L6 =>
                          .let_ (Op.mk (.and i32) (.var other, (.imm (1 : BitVec 32), ())))
                            fun lsb =>
                          .let_ (Op.mk (.cmp .ne i32) (.var lsb.1, (.imm (0 : BitVec 32), ())))
                            fun c2 =>
                          .jnz (.var c2.1) (
                            .let_ (Op.mk (.neg i32) (.imm (1 : BitVec 32), ())) fun n1 =>
                            .let_ (Op.mk (.trunc 32 8) (.var n1.1, ())) fun n8 =>
                            .let_ (Op.mk (.sext 8 32) (.var n8.1, ())) fun n32 =>
                            .jump L6.1 (.var n32.1, ())
                          ) (
                            .let_ (Op.mk (.trunc 32 8) (.imm (1 : BitVec 32), ())) fun p8 =>
                            .let_ (Op.mk (.sext 8 32) (.var p8.1, ())) fun p32 =>
                            .jump L6.1 (.var p32.1, ())
                          )
                        )
                    ) (.jump L4.1 ())
                  )
              ) .nil)
              (fun L3 =>
                .let_ (Op.mk (.zext 32 64) (.var ov_v.1, ())) fun z0 =>
                .let_ (Op.mk (.mul i64) (.var z0.1, (.imm (4 : BitVec 64), ()))) fun z1 =>
                .let_ (Op.mk (.add i64) (.var fl_p, (.var z1.1, ()))) fun pfl =>
                .load i32 (.var pfl.1) fun flv =>
                .let_ (Op.mk (.and i32) (.var flv, (.imm (1 : BitVec 32), ()))) fun fa =>
                .let_ (Op.mk (.cmp .ne i32) (.var fa.1, (.imm (0 : BitVec 32), ()))) fun ca =>
                .jnz (.var ca.1) (
                  .let_ (Op.mk (.cmp .ugt i64) (.var unass_v, (.imm (0 : BitVec 64), ())))
                    fun cu =>
                  .jnz (.var cu.1) (
                    .let_ (Op.mk (.sub i64) (.var unass_v, (.imm (1 : BitVec 64), ())))
                      fun un1 =>
                    .jump L3.1 (.var un1.1, ())
                  ) (.jump L3.1 (.var unass_v, ()))
                ) (.jump L3.1 (.var unass_v, ()))
              )
          )
        )
      ) (.jump L2.1 (.var tend_v, (.var unass_v, (.var unfl_v, ()))))
    )

def fastPropAlvlAssignExpr (nl_lvl cur_lvl csz other cref : Val i32)
    (rec_ph : Val .bool) (cbase ar_p tend_v unass_v unfl_v max_v vals_p fl_p lvl_p rsns_p
      tpos_p trl_p ph_p : Val i64)
    (k_next : Val i64 → Val i64 → Val i64 → Expr Val Cont [.bool]) :
    Expr Val Cont [.bool] :=
  .group (sig := [[i32]])
    (fun L17 => .cons (fun alvl_v =>
      fastPropAssignExpr other alvl_v.1 cref rec_ph tend_v unass_v unfl_v max_v vals_p fl_p lvl_p
        rsns_p tpos_p trl_p ph_p k_next) .nil)
    (fun L17 =>
      .let_ (Op.mk (.cmp .ult i32) (.var nl_lvl, (.var cur_lvl, ()))) fun clt =>
      .jnz (.var clt.1) (
        .group (sig := [[i32, i32]])
          (fun L23 => .cons (fun p =>
            .let_ (Op.mk (.cmp .ult i32) (.var p.2.1, (.var csz, ()))) fun cli =>
            .jnz (.var cli.1) (
              .let_ (Op.mk (.zext 32 64) (.var p.2.1, ())) fun li64 =>
              .let_ (Op.mk (.add i64) (.var cbase, (.var li64.1, ()))) fun idx0 =>
              .let_ (Op.mk (.mul i64) (.var idx0.1, (.imm (4 : BitVec 64), ()))) fun off4 =>
              .let_ (Op.mk (.add i64) (.var ar_p, (.var off4.1, ()))) fun par =>
              .load i32 (.var par.1) fun clit =>
              .group (sig := [[i32]])
                (fun L24 => .cons (fun mx_n =>
                  .let_ (Op.mk (.add i32) (.var p.2.1, (.imm (1 : BitVec 32), ()))) fun li1 =>
                  .jump L23.1 (.var mx_n.1, (.var li1.1, ()))
                ) .nil)
                (fun L24 =>
                  .let_ (Op.mk (.cmp .ne i32) (.var clit, (.var other, ()))) fun cne =>
                  .jnz (.var cne.1) (
                    .let_ (Op.mk (.lshr i32) (.var clit, (.imm (1 : BitVec 32), ())))
                      fun cv =>
                    .let_ (Op.mk (.zext 32 64) (.var cv.1, ())) fun cv64 =>
                    .let_ (Op.mk (.mul i64) (.var cv64.1, (.imm (4 : BitVec 64), ())))
                      fun cv4 =>
                    .let_ (Op.mk (.add i64) (.var lvl_p, (.var cv4.1, ()))) fun plv =>
                    .load i32 (.var plv.1) fun clv =>
                    .group (sig := [[i32]])
                      (fun L25 => .cons (fun mx2 => .jump L24.1 (.var mx2.1, ())) .nil)
                      (fun L25 =>
                        .let_ (Op.mk (.cmp .ugt i32) (.var clv, (.var p.1, ()))) fun cgt =>
                        .jnz (.var cgt.1) (.jump L25.1 (.var clv, ())) (.jump L25.1 (.var p.1, ()))
                      )
                  ) (.jump L24.1 (.var p.1, ()))
                )
            ) (.jump L17.1 (.var p.1, ()))
          ) .nil)
          (fun L23 => .jump L23.1 (.imm (0 : BitVec 32), (.imm (0 : BitVec 32), ())))
      ) (.jump L17.1 (.var nl_lvl, ()))
    )


theorem fastProp_assign_wp {Γ : Env} {c : FullCfg} {s st1 : FullState}
    {other alvl rsn : BitVec 32} {rec_ph : Bool}
    {tend_v unass_v unfl_v : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [.bool]} {X : XPost}
    {k_next : Val i64 → Val i64 → Val i64 → Expr Val Cont [.bool]}
    (hmaxv : c.max_vars < 2 * dimacsBound) (hcv0 : s.core.cur_vars ≤ c.max_vars)
    (hlen1_mem : (fastPropMem s st1).LengthsOk c)
    (hcv1 : st1.core.cur_vars = s.core.cur_vars)
    (hother_lt : other.toNat < 2 * st1.core.cur_vars)
    (hte_lt : st1.core.trail_end < st1.core.cur_vars)
    (htend_eq : tend_v.toNat = st1.core.trail_end)
    (hm : (FullMem c (fastPropMem s st1) ⋆ R) m)
    (hcont : ∀ (flags' : List (BitVec 32)) (ph' : List (BitVec 8))
        (unass_n unfl_n : BitVec 64) (m' : Mem 64),
      flags'.length = c.max_vars → ph'.length = c.max_vars →
      (FullMem c { fastPropMem s st1 with
        core := { (fastPropMem s st1).core with
          vals := (st1.core.vals.set other.toNat 1#8).set (other.toNat ^^^ 1) 0xFF#8
          flags := flags', lvl := st1.core.lvl.set (other.toNat / 2) alvl
          rsns := st1.core.rsns.set (other.toNat / 2)
            (if alvl = 0#32 then 0xFFFFFFFF#32 else rsn)
          trl := st1.core.trl.set st1.core.trail_end other
          trail_pos := st1.core.trail_pos.set (other.toNat / 2)
            (BitVec.ofNat 32 st1.core.trail_end) }
        scratch := { (fastPropMem s st1).scratch with phases := ph' } } ⋆ R) m' →
      wp Γ Q X (k_next (tend_v + 1#64) unass_n unfl_n) m') :
    wp Γ Q X (fastPropAssignExpr other alvl rsn rec_ph tend_v unass_v unfl_v
      (BitVec.ofNat 64 c.max_vars) c.pVals c.pFlags c.pLevel c.pReason c.pTrailPos c.pTrail
      c.pPhases k_next) m := by
  have hm_vals := hlen1_mem.core_ok.vals_len
  have hm_fl := hlen1_mem.core_ok.flags_len
  have hm_ph := hlen1_mem.scratch_ok.phases_len
  have hm_lvl := hlen1_mem.core_ok.lvl_len
  have hm_rsn := hlen1_mem.core_ok.rsns_len
  have hm_tp := hlen1_mem.core_ok.trail_pos_len
  have hm_trl := hlen1_mem.core_ok.trl_len
  unfold dimacsBound at hmaxv
  have hte_mv : st1.core.trail_end < c.max_vars := Nat.lt_of_lt_of_le hte_lt (hcv1 ▸ hcv0)
  have htend_max : tend_v.toNat < c.max_vars := htend_eq ▸ hte_mv
  refine wp_join_group
    (fun (tend_n, unass_n, unfl_n, ()) m_out => ∃ (flags' : List (BitVec 32))
      (ph' : List (BitVec 8)),
      tend_n = tend_v + 1#64 ∧ flags'.length = c.max_vars ∧ ph'.length = c.max_vars ∧
      (FullMem c { fastPropMem s st1 with
        core := { (fastPropMem s st1).core with
          vals := (st1.core.vals.set other.toNat 1#8).set (other.toNat ^^^ 1) 0xFF#8
          flags := flags', lvl := st1.core.lvl.set (other.toNat / 2) alvl
          rsns := st1.core.rsns.set (other.toNat / 2)
            (if alvl = 0#32 then 0xFFFFFFFF#32 else rsn)
          trl := st1.core.trl.set st1.core.trail_end other
          trail_pos := st1.core.trail_pos.set (other.toNat / 2)
            (BitVec.ofNat 32 st1.core.trail_end) }
        scratch := { (fastPropMem s st1).scratch with phases := ph' } } ⋆ R) m_out)
    ?_ ?_
  · rintro _ ⟨tend_n, unass_n, unfl_n, ⟨⟩⟩ m_out ⟨flags', ph', rfl, hfl', hph', hm_out⟩
    exact hcont flags' ph' unass_n unfl_n m_out hfl' hph' hm_out
  · intro Jtend hJtend
    fc_head_split
    · have htend_lt : tend_v.toNat < c.max_vars := by
        rwa [Nat.mod_eq_of_lt (Nat.lt_trans hmaxv (by decide))] at hc
      have hother1_lt : other.toNat ^^^ 1 < 2 * c.max_vars := by
        have h2cv : 2 * st1.core.cur_vars ≤ 2 * c.max_vars :=
          Nat.mul_le_mul_left 2 (hcv1 ▸ hcv0)
        rw [fc_nat_xor_one]
        by_cases hev : other.toNat % 2 = 0 <;> simp [hev] <;> omega
      fc_head_steps
      refine wp_join_group (fun (_unass_n, ()) mu => mu = m) ?_ ?_
      · rintro _ ⟨unass_n, ⟨⟩⟩ mu hmu
        subst mu
        fc_head_steps
        refine wp_join_group (fun () mph => ∃ ph' : List (BitVec 8),
          ph'.length = c.max_vars ∧
          (FullMem c { fastPropMem s st1 with
              core := { (fastPropMem s st1).core with
                vals := (st1.core.vals.set other.toNat 1#8).set (other.toNat ^^^ 1) 0xFF#8 }
              scratch := { (fastPropMem s st1).scratch with phases := ph' } } ⋆ R) mph) ?_ ?_
        · rintro _ ⟨⟩ mph ⟨ph', hph', hmph⟩
          fc_head_steps
          let rsn_v := if alvl = 0#32 then 0xFFFFFFFF#32 else rsn
          refine wp_join_group (fun (unfl_n, ()) m_as =>
            ∃ flags' : List (BitVec 32), flags'.length = c.max_vars ∧
            (FullMem c { fastPropMem s st1 with
                core := { (fastPropMem s st1).core with
                  vals := (st1.core.vals.set other.toNat 1#8).set (other.toNat ^^^ 1) 0xFF#8
                  flags := flags', lvl := st1.core.lvl.set (other.toNat / 2) alvl
                  rsns := st1.core.rsns.set (other.toNat / 2) rsn_v }
                scratch := { (fastPropMem s st1).scratch with phases := ph' } } ⋆ R) m_as) ?_ ?_
          · rintro _ ⟨unfl_n, ⟨⟩⟩ m_as ⟨flags', hfl', hm_as⟩
            fc_head_steps
            have htpos_eq : tend_v.setWidth 32 = BitVec.ofNat 32 st1.core.trail_end :=
              BitVec.eq_of_toNat_eq (by
                have hte32 : st1.core.trail_end < 2 ^ 32 :=
                  Nat.lt_trans hte_mv (Nat.lt_trans hmaxv (by decide))
                rw [BitVec.toNat_setWidth, htend_eq, Nat.mod_eq_of_lt hte32,
                  bv32_ofNat_toNat hte32])
            refine hJtend (tend_v + 1#64, unass_n, unfl_n, ()) m
              ⟨flags', ph', rfl, hfl', hph', ?_⟩
            simpa only [fastPropMem_trail_pos, fastPropMem_trl, htend_eq, htpos_eq,
              bv_c0_zext32_64, bv32_lshr_1] using hm
          · intro Junfl hJunfl; fc_head_steps
            · refine hJunfl (unfl_v + 1#64, ()) m
                ⟨(fastPropMem s st1).core.flags.set (other.toNat / 2)
                  ((fastPropMem s st1).core.flags[(other.toNat / 2)]'(by
                    rw [hm_fl]; exact Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_le hother_lt
                      (Nat.mul_le_mul_left 2 (hcv1 ▸ hcv0)))) &&& ~~~1#32),
                  ?_, ?_⟩
              · rw [List.length_set, hm_fl]
              · have hc0 : alvl = 0#32 := hc
                simpa only [rsn_v, hc0, ↓reduceIte, bv_c0_zext32_64, bv32_lshr_1,
                  ← BitVec.ofNat_eq_ofNat, fastPropMem_vals, fastPropMem_flags, fastPropMem_lvl,
                  fastPropMem_rsns] using hm
            · have hne0 : alvl ≠ 0#32 := hc
              refine hJunfl (unfl_v, ()) m ⟨(fastPropMem s st1).core.flags, hm_fl, ?_⟩
              simpa only [rsn_v, hne0, ↓reduceIte, bv_c0_zext32_64, bv32_lshr_1,
                fastPropMem_vals, fastPropMem_flags, fastPropMem_lvl, fastPropMem_rsns] using hm
        · intro Jph hJph
          have hm1_8 : BitVec.setWidth 8 (-1 : BitVec 32) = 0xFF#8 := by decide
          fc_head_split
          · fc_head_steps
            refine wp_join_group (fun (_pv32, ()) mpv => mpv = m) ?_ ?_
            · rintro _ ⟨pv32, ⟨⟩⟩ mpv hmpv
              subst mpv
              fc_head_steps
              exact hJph () m
                ⟨(fastPropMem s st1).scratch.phases.set (other.toNat / 2)
                    (BitVec.setWidth 8 pv32),
                  by rw [List.length_set, hm_ph],
                  by simpa only [fastPropMem_phases, fastPropMem_vals, bv_c0_zext32_64,
                    bv32_lshr_1, bv32_xor_1, hm1_8] using hm⟩
            · intro J6 hJ6; fc_head_steps
              · exact hJ6 _ m rfl
              · exact hJ6 _ m rfl
          · fc_head_steps
            exact hJph () m ⟨(fastPropMem s st1).scratch.phases, hm_ph, by
              simpa only [fastPropMem_vals, bv_c0_zext32_64, bv32_xor_1, hm1_8] using hm⟩
      · intro Jun hJun; fc_head_steps
        · simpa only [fastPropMem_flags] using hJun _ _ rfl
        · simpa only [fastPropMem_flags] using hJun _ _ rfl
        · simpa only [fastPropMem_flags] using hJun _ _ rfl
    · have hc' : ¬ tend_v.toNat < c.max_vars := by
        rwa [Nat.mod_eq_of_lt (Nat.lt_trans hmaxv (by decide))] at hc
      exact absurd htend_max hc'

theorem fastProp_large_assign_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s sem2 : FullState}
    {not_lit other cref nl_lvl0 cur_lvl csz32 : BitVec 32} {rec_ph : Bool}
    {off_v p_v q_v end_v tend_v unass_v unfl_v : BitVec 64}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    {k_next : Val i64 → Val i64 → Val i64 → Expr Val Cont [.bool]}
    (hmaxv : c.max_vars < 2 * dimacsBound) (har : c.arena_cap < 2 * dimacsBound)
    (hcv0 : s.core.cur_vars ≤ c.max_vars)
    (hpi2 : PropLitInv c F0 F_cur s sem2 not_lit.toNat off_v.toNat (q_v + 2#64).toNat
      (p_v.toNat + 2) end_v.toNat)
    (hlen2_mem : (fastPropMem s sem2).LengthsOk c)
    (hcr_lt : cref.toNat < 0x80000000)
    (hcr_ref : cref.toNat ∈ fullArenaClauseRefsCore sem2.core)
    (hng : fullArenaClauseGarbCore sem2.core cref.toNat = false)
    (hcr_fit : cref.toNat + 3 + fullArenaClauseSizeCore sem2.core cref.toNat ≤ sem2.core.arena_len)
    (hother_lt : other.toNat < 2 * sem2.core.cur_vars)
    (hov_un : sem2.core.vals[other.toNat]?.getD 0#8 = 0#8)
    (hnot_st : not_lit.toNat < 2 * sem2.core.cur_vars)
    (hother_mem : other.toNat ∈ fullArenaClauseLitsCore sem2.core cref.toNat)
    (hnot_mem : not_lit.toNat ∈ fullArenaClauseLitsCore sem2.core cref.toNat)
    (hunit : ∀ l ∈ fullArenaClauseLitsCore sem2.core cref.toNat,
      l = other.toNat ∨ sem2.core.vals[l]?.getD 0#8 = 0xFF#8)
    (hnl_eq : sem2.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0)
    (hcur_eq : cur_lvl = BitVec.ofNat 32 sem2.core.cur_level)
    (hcl32 : sem2.core.cur_level < 2 ^ 32)
    (hcsz32 : csz32.toNat = fullArenaClauseSizeCore sem2.core cref.toNat)
    (h3_idx : (cref.setWidth 64 + 3#64).toNat = cref.toNat + 3)
    (htend_eq : tend_v.toNat = sem2.core.trail_end)
    (hoom_eq : sem2.core.oom = 0#64) (hct_eq : sem2.core.confl_type = s.core.confl_type)
    (hm : (FullMem c (fastPropMem s sem2) ⋆ R) m)
    (hpost : ∀ (sem3 : FullState) (tend_n unass_n unfl_n : BitVec 64) (m' : Mem 64),
      PropLitInv c F0 F_cur s sem3 not_lit.toNat off_v.toNat (q_v + 2#64).toNat
        (p_v.toNat + 2) end_v.toNat →
      tend_n.toNat = sem3.core.trail_end → unass_n = sem3.core.unassigned →
      unfl_n = sem3.core.unflushed →
      sem3.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0 →
      sem3.core.oom = 0#64 → sem3.core.confl_type = s.core.confl_type →
      (FullMem c (fastPropMem s sem3) ⋆ R) m' →
      wp Γ Q X (k_next tend_n unass_n unfl_n) m') :
    wp Γ Q X (fastPropAlvlAssignExpr nl_lvl0 cur_lvl csz32 other cref rec_ph
      (cref.setWidth 64 + 3#64) c.pArena tend_v unass_v unfl_v (BitVec.ofNat 64 c.max_vars)
      c.pVals c.pFlags c.pLevel c.pReason c.pTrailPos c.pTrail c.pPhases k_next) m := by
  subst hcur_eq
  unfold dimacsBound at hmaxv har
  have haren2 := hpi2.len.core_ok.arena_len_arr
  have halen2_le := hpi2.len.core_ok.arena_len_le
  have hm2_aren := hlen2_mem.core_ok.arena_len_arr
  have hm2_lvl := hlen2_mem.core_ok.lvl_len
  have hfit_csz : cref.toNat + 3 + csz32.toNat ≤ c.arena_cap := by
    rw [hcsz32]; exact Nat.le_trans hcr_fit halen2_le
  have hwstk2 := hpi2.len.core_ok.wstk_len_arr
  have hte_lt : sem2.core.trail_end < sem2.core.cur_vars :=
    hpi2.nw.trail_end_lt_of_unassigned hother_lt hov_un
  have hmv64 : c.max_vars + 1 < 2 ^ 64 :=
    Nat.lt_trans (Nat.add_lt_add_right hmaxv 1) (by decide)
  have hte_mv : sem2.core.trail_end < c.max_vars :=
    Nat.lt_of_lt_of_le hte_lt (hpi2.cur_vars_eq ▸ hcv0)
  have htend1 : (tend_v + 1#64).toNat = sem2.core.trail_end + 1 := by
    rw [BitVec.toNat_add, htend_eq]
    change (sem2.core.trail_end + 1) % 2 ^ 64 = sem2.core.trail_end + 1
    exact Nat.mod_eq_of_lt (by omega)
  have hbd2 : cref.toNat + 3 + fullArenaClauseSizeCore sem2.core cref.toNat ≤
      sem2.core.arena.length := haren2 ▸ Nat.le_trans hcr_fit halen2_le
  have hkr_lt : ∀ {k}, k < fullArenaClauseSizeCore sem2.core cref.toNat →
      cref.toNat + 3 + k < sem2.core.arena.length := fun hk =>
    Nat.lt_of_lt_of_le (Nat.add_lt_add_left hk (cref.toNat + 3)) hbd2
  have hl_var : ∀ k (hk : k < fullArenaClauseSizeCore sem2.core cref.toNat),
      (sem2.core.arena[cref.toNat + 3 + k]'(hkr_lt hk)).toNat / 2 < c.max_vars := fun k hk =>
    Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_le
      (hpi2.nw.arena.lits_lt _ hcr_ref hng _ ((mem_fullArenaClauseLitsCore_iff hbd2).mpr
        ⟨k, hk, rfl⟩)) (Nat.mul_le_mul_left 2 (hpi2.cur_vars_eq ▸ hcv0)))
  have hcl64 : sem2.core.cur_level < 2 ^ 64 := Nat.lt_trans hcl32 (by decide)
  refine wp_join_group (fun (alvl_v, ()) ma => ma = m ∧
      (∀ l ∈ fullArenaClauseLitsCore sem2.core cref.toNat, l ≠ other.toNat →
        (sem2.core.lvl[l / 2]?.getD 0#32).toNat ≤ alvl_v.toNat) ∧
      (alvl_v = 0#32 ∨ ∃ l ∈ fullArenaClauseLitsCore sem2.core cref.toNat,
        l ≠ other.toNat ∧ alvl_v = sem2.core.lvl[l / 2]?.getD 0#32)) ?_ ?_
  · rintro _ ⟨alvl_v, ⟨⟩⟩ _ ⟨rfl, hmax_ge, hmax_att⟩
    refine fastProp_assign_wp hmaxv hcv0 hlen2_mem hpi2.cur_vars_eq hother_lt hte_lt htend_eq hm
      ?_
    intro flags' ph' unass_n unfl_n m' hfl' hph' hm'
    dsimp only at hm'
    rw [fastPropMem_assign_eq (te' := sem2.core.trail_end + 1)
      (un' := unass_n) (uf' := unfl_n)] at hm'
    have hassign := full_large_assign_nw_step hpi2.len.core_ok hpi2.nw hcr_lt hcr_ref hng hother_lt
      hov_un hnot_st hpi2.not_f hother_mem hunit hmax_ge hmax_att (flags' := flags')
      (unas' := unass_n) (unfl' := unfl_n)
    have ⟨hlen3, hnw3, hsw3, hag3, htr3, hperm3, hsc3, hnot_f3, hnl3⟩ :=
      fastPropMem_eq_of_eq hpi2 hpi2.sw hwstk2 hfl' hph' hnot_st hother_lt hov_un hnl_eq hassign
    exact hpost _ (tend_v + 1#64) unass_n unfl_n m'
      ⟨hlen3, hnw3, hsw3, hag3, htr3, hperm3, hsc3, hnot_f3⟩
      htend1 rfl rfl hnl3 hoom_eq hct_eq (by
        have hws_id : { sem2.core with wstk := sem2.core.wstk } = sem2.core := by
          cases sem2.core; rfl
        simpa only [hws_id] using hm')
  · intro Jalvl hJalvl; fc_head_split
    · fc_head_steps
      refine wp_loop_inv (ts := [i32, i32])
        (fun (mx_c, li_c, ()) m_li =>
          li_c.toNat ≤ fullArenaClauseSizeCore sem2.core cref.toNat ∧ m_li = m ∧
          (∀ k < li_c.toNat,
            (sem2.core.arena[cref.toNat + 3 + k]?.getD 0#32).toNat ≠ other.toNat →
            (sem2.core.lvl[(sem2.core.arena[cref.toNat + 3 + k]?.getD
              0#32).toNat / 2]?.getD 0#32).toNat ≤ mx_c.toNat) ∧
          (mx_c = 0#32 ∨ ∃ k < li_c.toNat,
            (sem2.core.arena[cref.toNat + 3 + k]?.getD 0#32).toNat ≠ other.toNat ∧
            mx_c = sem2.core.lvl[(sem2.core.arena[cref.toNat + 3 + k]?.getD
              0#32).toNat / 2]?.getD 0#32))
        (fun (_, li_c, ()) _ => fullArenaClauseSizeCore sem2.core cref.toNat - li_c.toNat)
        (fun L hL => by
          fc_head_steps
          exact hL _ m ⟨Nat.zero_le _, rfl, fun _ hk => by simp at hk, Or.inl rfl⟩)
        (fun L (mx_c, li_c, ()) m_li ⟨hli_le, hm_eq, hge, hatt⟩ ihi => by
          subst m_li
          fc_head_split
          · have hi_lt : li_c.toNat < fullArenaClauseSizeCore sem2.core cref.toNat :=
              hcsz32 ▸ hc
            have hidx_li : (cref.setWidth 64 + 3#64 + li_c.setWidth 64).toNat =
                cref.toNat + 3 + li_c.toNat := by
              rw [bv64_add_toNat (by
                rw [h3_idx, bv_c0_zext32_64]
                exact Nat.lt_of_lt_of_le (hkr_lt hi_lt)
                  (Nat.le_trans (Nat.le_of_eq haren2) (Nat.le_of_lt (Nat.lt_trans har
                    (by decide))))),
                h3_idx, bv_c0_zext32_64]
            have hli1 : (li_c + (1 : BitVec 32)).toNat = li_c.toNat + 1 := by
              rw [BitVec.toNat_add]
              exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hi_lt)
                (hcsz32 ▸ csz32.isLt))
            have hvar_lt := hl_var li_c.toNat hi_lt
            have hkr_idx : (cref.setWidth 64 + 3#64 + li_c.setWidth 64).toNat <
                sem2.core.arena.length := by
              rw [hidx_li]; exact hkr_lt hi_lt
            have hvar_lt_idx : (sem2.core.arena[(cref.setWidth 64 + 3#64 +
                li_c.setWidth 64).toNat]'hkr_idx).toNat / 2 < c.max_vars := by
              simp only [hidx_li]; exact hvar_lt
            let clit_v := sem2.core.arena[cref.toNat + 3 + li_c.toNat]'(hkr_lt hi_lt)
            let clv_v := sem2.core.lvl[clit_v.toNat / 2]'(by rw [hpi2.len.core_ok.lvl_len]; omega)
            have hcl_get : sem2.core.lvl[(sem2.core.arena[cref.toNat + 3 +
                li_c.toNat]?.getD 0#32).toNat / 2]?.getD 0#32 = clv_v := by
              rw [List.getElem?_eq_getElem (hkr_lt hi_lt), Option.getD_some,
                List.getElem?_eq_getElem (by rw [hpi2.len.core_ok.lvl_len]; omega),
                Option.getD_some]
            have hlv_eq : clv_v = sem2.core.lvl[((sem2.core.arena[(cref.setWidth 64 + 3#64 +
                li_c.setWidth 64).toNat]'hkr_idx) >>> (1 : Nat)).toNat]'(by
                rw [bv32_lshr_1, hpi2.len.core_ok.lvl_len]
                simp only [hidx_li]; exact hvar_lt) := by
              congr 1; simp only [bv32_lshr_1, hidx_li]; rfl
            have hidx_li_lt : (cref.setWidth 64 + 3#64 + li_c.setWidth 64).toNat < c.arena_cap := by
              rw [hidx_li]; omega
            have hdec : fullArenaClauseSizeCore sem2.core cref.toNat -
                (li_c + (1 : BitVec 32)).toNat <
                fullArenaClauseSizeCore sem2.core cref.toNat - li_c.toNat := by
              rw [hli1]; exact Nat.sub_lt (Nat.sub_pos_of_lt hi_lt) Nat.zero_lt_one
            fc_head_steps
            refine wp_join_group (fun (mx_n, ()) m24 => m24 = m ∧
              (clit_v.toNat ≠ other.toNat → clv_v.toNat ≤ mx_n.toNat) ∧
              mx_c.toNat ≤ mx_n.toNat ∧
              (mx_n = mx_c ∨ (clit_v.toNat ≠ other.toNat ∧ mx_n = clv_v))) ?_ ?_
            · rintro _ ⟨mx_n, ⟨⟩⟩ m24 ⟨hm24, hcl_le, hmx_le, hmx_src⟩
              subst m24
              fc_head_steps
              refine ihi _ m hdec ⟨by rw [hli1]; exact Nat.succ_le_of_lt hi_lt, rfl,
                fun k hk hne => ?_, ?_⟩
              · rw [hli1] at hk
                rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hk' | hki
                · exact Nat.le_trans (hge k hk' hne) hmx_le
                · subst hki; rw [hcl_get]
                  apply hcl_le
                  rw [List.getElem?_eq_getElem (hkr_lt hi_lt), Option.getD_some] at hne
                  exact hne
              · rcases hmx_src with rfl | ⟨hne, rfl⟩
                · exact hatt.imp id fun ⟨k, hk, hne, he⟩ =>
                    ⟨k, by rw [hli1]; exact Nat.lt_succ_of_lt hk, hne, he⟩
                · exact Or.inr ⟨li_c.toNat, by rw [hli1]; exact Nat.lt_succ_self _, fun heq => by
                    rw [List.getElem?_eq_getElem (hkr_lt hi_lt), Option.getD_some] at heq
                    exact hne heq, hcl_get.symm⟩
            · intro J24 hJ24; fc_head_split
              · have hne_o : clit_v.toNat ≠ other.toNat := fun heq => by
                  apply hc; apply BitVec.eq_of_toNat_eq
                  simpa only [fastPropMem_arena,
                    Nat.mod_eq_of_lt (by omega : cref.toNat + 3 + li_c.toNat < 2 ^ 64)] using heq
                fc_head_steps
                refine wp_join_group (fun (mx2, ()) m25 => m25 = m ∧
                  clv_v.toNat ≤ mx2.toNat ∧ mx_c.toNat ≤ mx2.toNat ∧
                  (mx2 = mx_c ∨ mx2 = clv_v)) ?_ ?_
                · rintro _ ⟨mx2, ⟨⟩⟩ m25 ⟨hm25, h1, h2, hsrc⟩
                  subst m25
                  fc_head_steps
                  exact hJ24 (mx2, ()) m ⟨rfl, fun _ => h1, h2, hsrc.imp id fun he => ⟨hne_o, he⟩⟩
                · intro J25 hJ25; fc_head_steps
                  · have hkr_idx_m : (cref.setWidth 64 + 3#64 + li_c.setWidth 64).toNat <
                        (fastPropMem s sem2).core.arena.length := by
                      rw [fastPropMem_arena]; exact hkr_idx
                    have hclv_mem : ∀ hp, ((fastPropMem s sem2).core.lvl[(BitVec.setWidth 64
                        ((fastPropMem s sem2).core.arena[(cref.setWidth 64 + 3#64 +
                          li_c.setWidth 64).toNat]'hkr_idx_m >>> 1)).toNat]'hp) = clv_v :=
                      fun hp => by
                        dsimp only [clv_v]
                        have h1 : (BitVec.setWidth 64 ((fastPropMem s sem2).core.arena[(
                            cref.setWidth 64 + 3#64 + li_c.setWidth 64).toNat]'hkr_idx_m >>>
                              1)).toNat = clit_v.toNat / 2 := by
                          rw [bv_c0_zext32_64, bv32_lshr_1]
                          exact congrArg (·.toNat / 2)
                            ((fc_getElem_arena s sem2).trans
                              (fc_getElem_eq_of_idx hidx_li _ (hkr_lt hi_lt)))
                        exact (fc_getElem_lvl s sem2).trans (fc_getElem_eq_of_idx h1 _ _)
                    have hgt : mx_c.toNat < clv_v.toNat := by
                      have hc' := hc
                      simp only [fastPropMem_lvl, fastPropMem_arena,
                        Nat.mod_eq_of_lt (by omega : cref.toNat + 3 + li_c.toNat < 2 ^ 64)]
                        at hc'
                      exact hc'
                    refine hJ25 (_, ()) m ⟨rfl, ?_, ?_, Or.inr (hclv_mem _)⟩
                    · simp only [hclv_mem]; exact Nat.le_refl _
                    · simp only [hclv_mem]; exact Nat.le_of_lt hgt
                  · have hle : clv_v.toNat ≤ mx_c.toNat := by
                      have hnot_gt : ¬ mx_c.toNat < clv_v.toNat := by
                        have hc' := hc
                        simp only [fastPropMem_lvl, fastPropMem_arena,
                          Nat.mod_eq_of_lt (by omega : cref.toNat + 3 + li_c.toNat < 2 ^ 64)]
                          at hc'
                        exact hc'
                      exact Nat.le_of_not_lt hnot_gt
                    exact hJ25 (mx_c, ()) m ⟨rfl, hle, Nat.le_refl _, Or.inl rfl⟩
              · have hcl_eq : clit_v.toNat = other.toNat := by
                  have hh := congrArg BitVec.toNat hc
                  simpa only [fastPropMem_arena,
                    Nat.mod_eq_of_lt (by omega : cref.toNat + 3 + li_c.toNat < 2 ^ 64)] using hh
                fc_head_steps
                exact hJ24 (mx_c, ()) m
                  ⟨rfl, fun hne => absurd hcl_eq hne, Nat.le_refl _, Or.inl rfl⟩
          · have hi_eq : li_c.toNat = fullArenaClauseSizeCore sem2.core cref.toNat := by
              change ¬ li_c.toNat < csz32.toNat at hc
              exact Nat.le_antisymm hli_le (hcsz32 ▸ Nat.le_of_not_lt hc)
            fc_head_steps
            refine hJalvl _ m ⟨rfl, fun l hl hne => ?_, ?_⟩
            · obtain ⟨k, hk, hget⟩ := (mem_fullArenaClauseLitsCore_iff hbd2).mp hl
              have hk' := hge k (hi_eq ▸ hk)
              rw [List.getElem?_eq_getElem (hkr_lt hk), Option.getD_some, hget] at hk'
              exact hk' hne
            · refine hatt.elim Or.inl fun ⟨k, hk, hne, hres⟩ => ?_
              have hk' : k < fullArenaClauseSizeCore sem2.core cref.toNat := hi_eq ▸ hk
              rw [List.getElem?_eq_getElem (hkr_lt hk'), Option.getD_some] at hne hres
              exact Or.inr ⟨(sem2.core.arena[cref.toNat + 3 + k]'(hkr_lt hk')).toNat,
                (mem_fullArenaClauseLitsCore_iff hbd2).mpr ⟨k, hk', rfl⟩, hne, hres⟩)
    · have hnot_ult : nl_lvl0.ult (BitVec.ofNat 32 sem2.core.cur_level) = false := by
        have hnot_lt_cl : ¬ nl_lvl0.toNat < sem2.core.cur_level := by
          simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl32] using hc
        rw [BitVec.ult_eq_decide]
        exact decide_eq_false (by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl32]; exact hnot_lt_cl)
      have ⟨hge, hatt⟩ := fastProp_nonchrono_alvl hpi2.nw hcr_ref hng hpi2.not_f
        hov_un hnot_mem hunit hnl_eq hnot_ult hcl32
      fc_head_steps
      exact hJalvl _ m ⟨rfl, hge, hatt⟩


def fastPropFinishExpr (h_p pWvec pWstk : Val i64) (not_lit : Val i32)
    (off_v tend_v unass_v unfl_v ticks_v p_v q_v end_v : Val i64) (confl_v : Val .bool) :
    Expr Val Cont [.bool] :=
  .group (sig := [[i64, i64]])
    (fun L1 => .cons (fun q =>
      .let_ (Op.mk (.cmp .ult i64) (.var q.1, (.var end_v, ()))) fun v88 =>
      .jnz (.var v88.1) (
        .let_ (Op.mk (.mul i64) (.var q.2.1, (.imm (4 : BitVec 64), ()))) fun v89 =>
        .let_ (Op.mk (.add i64) (.var pWstk, (.var v89.1, ()))) fun v90 =>
        .let_ (Op.mk (.mul i64) (.var q.1, (.imm (4 : BitVec 64), ()))) fun v91 =>
        .let_ (Op.mk (.add i64) (.var pWstk, (.var v91.1, ()))) fun v92 =>
        .load i32 (.var v92.1) fun v93 =>
        .store (.var v93) (.var v90.1) (
          .let_ (Op.mk (.add i64) (.var q.2.1, (.imm (1 : BitVec 64), ()))) fun v94 =>
          .let_ (Op.mk (.add i64) (.var q.1, (.imm (1 : BitVec 64), ()))) fun v95 =>
          .jump L1.1 (.var v95.1, (.var v94.1, ()))
        )
      ) (
        .let_ (Op.mk (.zext 32 64) (.var not_lit, ())) fun v89 =>
        .let_ (Op.mk (.sext 32 64) (.imm (1 : BitVec 32), ())) fun v90 =>
        .let_ (Op.mk (.shl i64) (.var v89.1, (.var v90.1, ()))) fun v91 =>
        .let_ (Op.mk (.add i64) (.var v91.1, (.imm (1 : BitVec 64), ()))) fun v92 =>
        .let_ (Op.mk (.mul i64) (.var v92.1, (.imm (4 : BitVec 64), ()))) fun v93 =>
        .let_ (Op.mk (.add i64) (.var pWvec, (.var v93.1, ()))) fun v94 =>
        .let_ (Op.mk (.sub i64) (.var q.2.1, (.var off_v, ()))) fun v95 =>
        .let_ (Op.mk (.trunc 64 32) (.var v95.1, ())) fun v96 =>
        .store (.var v96.1) (.var v94.1) (
          .let_ (Op.mk (.add i64) (.var h_p, (.imm (464 : BitVec 64), ()))) fun v97 =>
          .load i64 (.var v97.1) fun v98 =>
          .let_ (Op.mk (.sub i64) (.var end_v, (.var q.2.1, ()))) fun v99 =>
          .let_ (Op.mk (.add i64) (.var v98, (.var v99.1, ()))) fun v100 =>
          .let_ (Op.mk (.add i64) (.var h_p, (.imm (464 : BitVec 64), ()))) fun v101 =>
          .store (.var v100.1) (.var v101.1) (
            .let_ (Op.mk (.add i64) (.var h_p, (.imm (144 : BitVec 64), ()))) fun v102 =>
            .store (.var tend_v) (.var v102.1) (
              .let_ (Op.mk (.add i64) (.var h_p, (.imm (792 : BitVec 64), ()))) fun v103 =>
              .store (.var unass_v) (.var v103.1) (
                .let_ (Op.mk (.add i64) (.var h_p, (.imm (512 : BitVec 64), ()))) fun v104 =>
                .store (.var unfl_v) (.var v104.1) (
                  .let_ (Op.mk (.add i64) (.var h_p, (.imm (600 : BitVec 64), ()))) fun v105 =>
                  .load i64 (.var v105.1) fun v106 =>
                  .let_ (Op.mk (.add i64) (.var v106, (.var ticks_v, ()))) fun v107 =>
                  .let_ (Op.mk (.add i64) (.var h_p, (.imm (600 : BitVec 64), ()))) fun v108 =>
                  .store (.var v107.1) (.var v108.1) (
                    .let_ (Op.mk (.not .bool) (.var confl_v, ())) fun v109 =>
                    .ret (.var v109.1, ())
                  )
                )
              )
            )
          )
        )
      )
    ) .nil)
    (fun L1 => .jump L1.1 (.var p_v, (.var q_v, ())))

theorem fastProp_finish_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sem : FullState} {not_lit : BitVec 32}
    {off_v tend_v unass_v unfl_v ticks_v p_v q_v end_v ignore_ref : BitVec 64}
    {confl_v : Bool} {R : Mem 64 → Prop} {mb : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hwc : c.wcap < 2 * dimacsBound) (_hcv0 : s.core.cur_vars ≤ c.max_vars)
    (hdense0 : s.core.dense_mode = 0#64) (hnot_lt : not_lit.toNat < 2 * s.core.cur_vars)
    (hpi : PropLitInv c F0 F_cur s sem not_lit.toNat off_v.toNat q_v.toNat p_v.toNat end_v.toNat)
    (htend_eq : tend_v.toNat = sem.core.trail_end) (hunass_eq : unass_v = sem.core.unassigned)
    (hunfl_eq : unfl_v = sem.core.unflushed)
    (hcf_f : confl_v = false → sem.core.oom = 0#64 ∧ sem.core.confl_type = s.core.confl_type)
    (hcf_t : confl_v = true → PropLitConfl F_cur ignore_ref sem.core)
    (hmb : (FullMem c (fastPropMem s sem) ⋆ R) mb)
    (hret_st : ∀ (ok : Bool) (st : FullState) (ml : Mem 64),
      st.LengthsOk c → FullWitnessInv c F0 F_cur st.core →
      AgreesExcept propLitCoreMask s.core st.core →
      FullPropDecSpecs.FullTrailExt s.core st.core →
      FullPropDecSpecs.FullArenaPermEq s.core st.core →
      st.scratch = { s.scratch with
        search_ticks := st.scratch.search_ticks, wsort := st.scratch.wsort,
        phases := st.scratch.phases } →
      (ok = false → PropLitConfl F_cur ignore_ref st.core) →
      (ok = true → st.core.oom = 0#64 ∧ st.core.confl_type = s.core.confl_type) →
      (FullMem c st ⋆ R) ml → Q (ok, ()) ml) :
    wp Γ Q X (fastPropFinishExpr c.hdr c.pWvec c.pWstk not_lit off_v tend_v unass_v unfl_v
      ticks_v p_v q_v end_v confl_v) mb := by
  have hnot_st : not_lit.toNat < 2 * sem.core.cur_vars := hpi.cur_vars_eq.symm ▸ hnot_lt
  have ⟨hend_le, hwlen_le⟩ := hpi.end_lt_wcap hnot_st
  have hend_wcap : end_v.toNat ≤ c.wcap := Nat.le_trans hend_le hwlen_le
  unfold dimacsBound at hwc
  have hwc64 : c.wcap + 1 < 2 ^ 64 := Nat.lt_trans (Nat.add_lt_add_right hwc 1) (by decide)
  have hq_ge := hpi.sw.q_ge; have hq_le := hpi.sw.q_le_p; have hp_le := hpi.sw.p_le_end
  have hwstk_len := hpi.len.core_ok.wstk_len_arr; have hwvec_len := hpi.len.core_ok.wvec_len
  have hwvec_mem : (fastPropMem s sem).core.wvec.length = 4 * c.max_vars := by
    rw [fastPropMem_wvec]; exact hwvec_len
  have hidx1_nat :
      ((not_lit.setWidth 64 <<< (1 : Nat)) + (1 : BitVec 64)).toNat = 2 * not_lit.toNat + 1 :=
    fc_bv64_shl1_add1_nat not_lit
  let q_fin : Nat := q_v.toNat + (end_v.toNat - p_v.toNat)
  unfold fastPropFinishExpr
  refine wp_loop_inv
    (fun (p_c, q_c, ()) m2 => ∃ wstk_c : List (BitVec 32),
      wstk_c.length = c.wcap ∧ p_v.toNat ≤ p_c.toNat ∧ p_c.toNat ≤ end_v.toNat ∧
      q_c.toNat = q_v.toNat + (p_c.toNat - p_v.toNat) ∧
      (∀ k, off_v.toNat ≤ k → k < q_v.toNat → wstk_c[k]? = sem.core.wstk[k]?) ∧
      (∀ k < p_c.toNat - p_v.toNat, wstk_c[q_v.toNat + k]? = sem.core.wstk[p_v.toNat + k]?) ∧
      (∀ k, p_c.toNat ≤ k → k < end_v.toNat → wstk_c[k]? = sem.core.wstk[k]?) ∧
      (∀ k, (k < off_v.toNat ∨ end_v.toNat ≤ k) → wstk_c[k]? = sem.core.wstk[k]?) ∧
      (FullMem c (fastPropMem s { sem with core := { sem.core with wstk := wstk_c } }) ⋆ R) m2)
    (fun (p_c, _, ()) _ => end_v.toNat - p_c.toNat)
    (fun L2 hL2 => by
      fc_head_steps
      exact hL2 (p_v, q_v, ()) mb ⟨sem.core.wstk, hwstk_len, Nat.le_refl _, hp_le, by omega,
        fun _ _ _ => rfl, fun _ hk => by omega, fun _ _ _ => rfl, fun _ _ => rfl, hmb⟩)
    (fun L2 (p_c, q_c, ()) m2 ⟨wstk_c, hwl2, hp_ge, hp_le2, hqc_eq,
        hpre, hsuf, hrem, hout, hm2⟩ ih2 => ?_)
  fc_head_steps
  · have hp_lt : p_c.toNat < end_v.toNat := hc
    have hstep := propLit_loop2_step hq_ge hq_le hp_ge hp_lt (by omega) (by omega)
      hpre hsuf hrem hout
    have hpc_add : (p_c + (1 : BitVec 64)).toNat = p_c.toNat + 1 := bv64_add1_toNat (by omega)
    have hqc_add : (q_c + (1 : BitVec 64)).toNat =
        q_v.toNat + ((p_c + (1 : BitVec 64)).toNat - p_v.toNat) := by
      rw [bv64_add1_toNat (by omega), hpc_add]; omega
    refine ih2 (p_c + (1 : BitVec 64), q_c + (1 : BitVec 64), ()) m (by dsimp only; omega)
      ⟨wstk_c.set q_c.toNat (wstk_c[p_c.toNat]'(by omega)), by simp [hwl2],
        by omega, by omega, hqc_add, ?_, ?_, ?_, ?_, by
          simpa only [fastPropMem_wstk, fastPropMem_with_wstk] using hm⟩
    · simpa only [← hqc_eq] using hstep.1
    · rw [hpc_add]; simpa only [← hqc_eq] using hstep.2.1
    · rw [hpc_add]; simpa only [← hqc_eq] using hstep.2.2.1
    · simpa only [← hqc_eq] using hstep.2.2.2
  · have hpc_eq : p_c.toNat = end_v.toNat := by c0_bound
    have hqfin_eq : q_c.toNat = q_fin := by dsimp [q_fin]; omega
    let sem' : FullState :=
      { sem with scratch :=
          { sem.scratch with search_ticks := s.scratch.search_ticks + ticks_v } }
    have hpi' : PropLitInv c F0 F_cur s sem' not_lit.toNat off_v.toNat q_v.toNat p_v.toNat
        end_v.toNat :=
      { len := ⟨hpi.len.core_ok, hpi.len.scratch_ok.with_ticks _⟩
        nw := hpi.nw, sw := hpi.sw, ag := hpi.ag, tr := hpi.tr, perm := hpi.perm
        sc_eq := by dsimp only [sem']; rw [hpi.sc_eq]
        not_f := hpi.not_f }
    have hm_rew :
        (FullMem c { sem' with core := { sem'.core with
            wstk := wstk_c
            wvec := sem'.core.wvec.set (2 * not_lit.toNat + 1) ((q_c - off_v).setWidth 32)
            wusable := sem'.core.wusable + (end_v - q_c) } } ⋆ R) m := by
      simp only [hidx1_nat, fastPropMem_wvec, fastPropMem_wusable, fastPropMem_search_ticks] at hm
      rw [htend_eq, hunass_eq, hunfl_eq] at hm
      rw [fastPropMem_finish_eq] at hm
      exact hm
    have ⟨hl_f, hw_f, hag_f, htr_f, hperm_f, hsc_f, hcf_f', hoom_f, hm_f⟩ :=
      propLit_finish (ctype0 := s.core.confl_type) hpi' hdense0 hnot_st hwl2 hqfin_eq rfl
        hpre (fun k hk => hsuf k (by omega)) hout (fun _ _ => rfl) hcf_f hcf_t hm_rew
    exact hret_st (!confl_v) _ m hl_f hw_f hag_f htr_f hperm_f hsc_f hcf_f' hoom_f hm_f

end LeanQbe.T.Examples.Kissat.FastCore
