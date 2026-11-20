module

public import LeanQbe.T.Examples.Kissat.PlainPropLemmas1
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Plain` BCP `Func.wp` Proofs (`Stage 3`, Wave 2b Shard 3, Part 2)

Builds on `PlainPropLemmas1` to prove parametric `(Γ : Env)` `Func.wp` contracts for:
1. `plain_prop_lit` (`plain_prop_lit_wp` → `plainPropLitSpec`)
2. `plain_propagate` (`plain_propagate_wp` → `plainPropagateSpec`)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Plain

open Std Std.Sat Std.ExtHashMap LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
  LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat Kraken.Bedrock2.Test
open scoped PlainPropTactics

/-! ## 1. Framing masks & `plain_propagate` `Func.wp` proof -/

private theorem PlainCoreInv.with_fuel_prop {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (h : PlainCoreInv c F0 s) {fuel' : BitVec 64} {prop' : Nat} (hp : prop' ≤ s.trail_end) :
    PlainCoreInv c F0 { s with fuel := fuel', propagated := prop' } :=
  { h with
    lengths := { h.lengths with propagated_le := hp }
    arena := { h.arena with len_ok := h.arena.len_ok }
    watches := h.watches.with_wstk rfl rfl rfl rfl }

private def propMask (h0 : PlainHeur) (t : PlainState) : PlainState :=
  { t with
    vals := [], lvl := [], rsns := [], trl := [], trail_pos := [], trail_end := 0,
    propagated := 0, unflushed := 0#64, wvec := [], arena := [], wstk := [], wlen := 0,
    wusable := 0#64, fuel := 0#64, confl_type := 0#64, confl_ref := 0#64,
    confl_lit0 := 0#64, confl_lit1 := 0#64, oom := 0#64, heur := h0 }

private theorem prop_eq_upd {h0 : PlainHeur} {s st : PlainState}
    (h : AgreesExcept (propMask h0) s st) :
    st = { s with
      vals := st.vals, lvl := st.lvl, rsns := st.rsns, trl := st.trl, trail_pos := st.trail_pos,
      trail_end := st.trail_end, propagated := st.propagated, unflushed := st.unflushed,
      wvec := st.wvec, arena := st.arena, wstk := st.wstk, wlen := st.wlen, wusable := st.wusable,
      fuel := st.fuel, confl_type := st.confl_type, confl_ref := st.confl_ref,
      confl_lit0 := st.confl_lit0, confl_lit1 := st.confl_lit1, oom := st.oom,
      heur := st.heur } := by
  have := h.get PlainState.d_cur; have := h.get PlainState.d_val; have := h.get PlainState.arena_len
  have := h.get PlainState.arena_garbage; have := h.get PlainState.first_reducible
  have := h.get PlainState.num_irred; have := h.get PlainState.num_redundant
  have := h.get PlainState.num_binary; have := h.get PlainState.probing
  have := h.get PlainState.cur_level; have := h.get PlainState.tmp_cnt
  have := h.get PlainState.tmp_len; have := h.get PlainState.min_clr_len
  have := h.get PlainState.min_clr_full; have := h.get PlainState.mrk; have := h.get PlainState.tmp
  have := h.get PlainState.min_stk; have := h.get PlainState.min_clr
  cases st; cases s; simp only at *; subst_vars; rfl

theorem plain_propagate_wp (Γ : Env)
    (hPropLit : ∀ args m Q X, plainPropLitSpec args m Q X →
      Γ "plain_prop_lit" [i64, i32] [.bool] args m Q X) :
    ∀ args m Q X, plainPropagateSpec args m Q X →
      Func.wp Γ plain_propagate_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩
  have hmv := c.hmv; unfold dimacsBound at hmv
  let EmptyW : Prop := ∀ l < 2 * c.mv, watchSize s l = 0
  have hret_st : ∀ (r : BitVec 64) (st : PlainState) (ml : Mem 64),
      PlainCoreInv c F0 st → AgreesExcept (propMask s.heur) s st →
      TrailExt s st → st.fuel.toNat ≤ s.fuel.toNat →
      st.heur.rel_trigger = s.heur.rel_trigger →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 0#64 → st.propagated = st.trail_end ∧ (s.oom = 0#64 → st.oom = 0#64)) →
      (r = 1#64 →
        st.fuel.toNat < s.fuel.toNat ∧ st.oom = 0#64 ∧
        ((st.confl_type = 1#64 ∧ st.confl_lit0.toNat < 2 * c.mv ∧
          st.confl_lit1.toNat < 2 * c.mv ∧
          F0.EntailsClause (cnfClause [st.confl_lit0.toNat, st.confl_lit1.toNat]) ∧
          st.vals[st.confl_lit0.toNat]?.getD 0#8 = 0xFF#8 ∧
          st.vals[st.confl_lit1.toNat]?.getD 0#8 = 0xFF#8) ∨
         (st.confl_type = 2#64 ∧ st.confl_ref.toNat ∈ arenaClauseRefs st ∧
          arenaClauseGarb st st.confl_ref.toNat = false ∧
          ∀ l ∈ arenaClauseLits st st.confl_ref.toNat, st.vals[l]?.getD 0#8 = 0xFF#8))) →
      (s.oom = 0#64 → EmptyW → s.trail_end - s.propagated ≤ s.fuel.toNat →
        r = 0#64 ∧ st.vals = s.vals ∧ st.trail_end = s.trail_end ∧
        st.propagated = s.trail_end ∧ st.wvec = s.wvec ∧ st.oom = 0#64 ∧
        st.fuel.toNat = s.fuel.toNat - (s.trail_end - s.propagated)) →
      (s.propagated = s.trail_end → r = 0#64 ∧ st = s) →
      (PlainMem c st ⋆ R) ml → Q (r, ()) ml := by
    intro r st ml hst hag htr hfl hrel hr hr0 hr1 hemp hnoop hml
    have hst_eq := prop_eq_upd hag
    have hst' := hst; rw [hst_eq] at hst' hml
    refine hQ r st.vals st.lvl st.rsns st.trl st.trail_pos st.trail_end st.propagated st.unflushed
      st.wvec st.arena st.wstk st.wlen st.wusable st.fuel st.confl_type st.confl_ref
      st.confl_lit0 st.confl_lit1 st.oom st.heur ml hst' htr.te_ge hfl hrel
      htr.trl_pref htr.lvl_pres htr.new_lvl hr hr0 ?_ hemp ?_ hml
    · intro h1; simpa only [← hst_eq] using hr1 h1
    · intro hpe; obtain ⟨h0, heq⟩ := hnoop hpe; exact ⟨h0, hst_eq ▸ heq⟩
  pp_steps
  refine wp_loop_group
    (fun rem () ml => ∃ st : PlainState,
      rem = st.fuel.toNat ∧ PlainCoreInv c F0 st ∧ AgreesExcept (propMask s.heur) s st ∧
      TrailExt s st ∧ st.fuel.toNat ≤ s.fuel.toNat ∧
      st.heur.rel_trigger = s.heur.rel_trigger ∧
      (s.oom = 0#64 → st.oom = 0#64) ∧
      (s.oom = 0#64 → EmptyW →
        st.wvec = s.wvec ∧ st.vals = s.vals ∧ st.trail_end = s.trail_end ∧
        s.propagated ≤ st.propagated ∧
        st.fuel.toNat + (st.propagated - s.propagated) = s.fuel.toNat) ∧
      (s.propagated = s.trail_end → st = s) ∧
      (PlainMem c st ⋆ R) ml) ?_ ?_
  · rintro L rem ⟨⟩ ml ih
      ⟨st, rfl, hst_inv, hag, htr, hfuel_le, hrel, hoom_pres, hempty, hnoop, hml⟩
    have hlen := hst_inv.lengths
    have htl := hlen.trl_len; have hte_le := hlen.trail_end_le; have hpr_le := hlen.propagated_le
    pp_steps
    · have hpr_lt : st.propagated < st.trail_end := by c0_bound
      have hne_end : s.propagated ≠ s.trail_end := fun h => by have := hnoop h; subst this; omega
      refine hret_st 2#64 st ml hst_inv hag htr hfuel_le hrel (Or.inr (Or.inr rfl))
        (by simp) (by simp) (fun hoom0 _ _ => absurd (hoom_pres hoom0) hc)
        (fun h => absurd h hne_end) hml
    · have hpr_lt : st.propagated < st.trail_end := by c0_bound
      have hne_end : s.propagated ≠ s.trail_end := fun h => by have := hnoop h; subst this; omega
      refine hret_st 2#64 st ml hst_inv hag htr hfuel_le hrel (Or.inr (Or.inr rfl))
        (by simp) (by simp) (fun hoom0 hE hle => ?_) (fun h => absurd h hne_end) hml
      obtain ⟨_, _, hte_eq, _, hsum⟩ := hempty hoom0 hE
      have hfz : st.fuel.toNat = 0 := by rw [hc]; rfl
      omega
    · have hpr_lt : st.propagated < st.trail_end := by c0_bound
      have hne_end : s.propagated ≠ s.trail_end := fun h => by have := hnoop h; subst this; omega
      have hoom0_st : st.oom = 0#64 := by assumption
      have hfuel_sub : (st.fuel - 1#64).toNat = st.fuel.toNat - 1 := bv64_sub1_toNat hc
      have hfuel_pos : 0 < st.fuel.toNat :=
        Nat.pos_of_ne_zero fun h0 => hc (BitVec.eq_of_toNat_eq (by simpa using h0))
      have hpr1 : (BitVec.ofNat 64 st.propagated + 1#64).toNat = st.propagated + 1 := by c0_bound
      have hidx : (BitVec.ofNat 64 st.propagated).toNat = st.propagated := by c0_bound
      let st1 : PlainState := { st with
        fuel := st.fuel - 1#64, propagated := (BitVec.ofNat 64 st.propagated + 1#64).toNat }
      have hlit_lt : (st.trl[(BitVec.ofNat 64 st.propagated).toNat]'(by c0_bound)).toNat <
          2 * c.mv := by
        simpa [hidx, List.getElem?_eq_getElem (show st.propagated < st.trl.length by omega)]
          using hst_inv.trail_lits_lt st.propagated hpr_lt
      have hnlit_lt : (st.trl[(BitVec.ofNat 64 st.propagated).toNat]'(by c0_bound) ^^^ 1#32).toNat <
          2 * c.mv := by simpa [BitVec.toNat_xor] using litNeg_lt_two_mul hlit_lt
      c0_call hPropLit
      refine ⟨c, F0, st1, R, rfl, hst_inv.with_fuel_prop (by omega), hoom0_st, hm,
        fun ok vals' lvl' rsns' trl' tp' te' unfl' wvec' arena' wstk' wlen' wu'
          ctype' cref' c0' c1' oom' heur' m2 hst2_inv hte2 hrel2 htrl2 hlvl2 hnew2
          hconfl hws0 hok_oom hm2 => ?_⟩
      let st2 : PlainState :=
        { st1 with
          vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
          trail_end := te', unflushed := unfl', wvec := wvec', arena := arena', wstk := wstk',
          wlen := wlen', wusable := wu', confl_type := ctype', confl_ref := cref',
          confl_lit0 := c0', confl_lit1 := c1', oom := oom', heur := heur' }
      have htr2 : TrailExt s st2 :=
        (⟨htr.te_ge, htr.trl_pref, htr.lvl_pres, htr.new_lvl⟩ : TrailExt s st1).trans
          ⟨hte2, htrl2, hlvl2, hnew2⟩ (hag.get PlainState.cur_level)
      have hag1 : AgreesExcept (propMask s.heur) s st1 :=
        hag.update (fun t => { t with fuel := st1.fuel, propagated := st1.propagated })
      have hag2 : AgreesExcept (propMask s.heur) s st2 :=
        hag1.update (fun t => { t with
          vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
          trail_end := te', unflushed := unfl', wvec := wvec', arena := arena', wstk := wstk',
          wlen := wlen', wusable := wu', confl_type := ctype', confl_ref := cref',
          confl_lit0 := c0', confl_lit1 := c1', oom := oom', heur := heur' })
      have hws_e : s.oom = 0#64 → EmptyW →
          watchSize st1 (st.trl[(BitVec.ofNat 64 st.propagated).toNat]'(
            by c0_bound) ^^^ 1#32).toNat = 0 := fun hoom0 hE => by
        unfold watchSize; dsimp [st1]; rw [(hempty hoom0 hE).1]; exact hE _ hnlit_lt
      pp_steps
      · have hok_t : ok = true := by assumption
        refine ih st2.fuel.toNat () m2 (by dsimp [st2, st1]; omega)
          ⟨st2, rfl, hst2_inv, hag2, htr2,
            by dsimp [st2, st1]; omega, hrel2.trans hrel,
            fun _ => hok_oom hok_t, fun hoom0 hE => ?_,
            fun h => absurd h hne_end, hm2⟩
        obtain ⟨hwv_eq, hvals_eq, hte_eq, _, _⟩ := hempty hoom0 hE
        have hst2_eq : st2 = st1 := (hws0 (hws_e hoom0 hE)).2
        rw [hst2_eq]; dsimp only [st1]; rw [hpr1, hfuel_sub]
        exact ⟨hwv_eq, hvals_eq, hte_eq, by omega, by omega⟩
      · have hok_f : ok = false := by assumption
        refine hret_st 2#64 st2 m2 hst2_inv hag2 htr2
          (by dsimp [st2, st1]; omega) (hrel2.trans hrel) (Or.inr (Or.inr rfl))
          (by simp) (by simp) (fun hoom0 hE _ => ?_) (fun h => absurd h hne_end) hm2
        have hok_t := (hws0 (hws_e hoom0 hE)).1; rw [hok_f] at hok_t; cases hok_t
      · have hok_f : ok = false := by assumption
        have hoom2_0 : oom' = 0#64 := by assumption
        refine hret_st 1#64 st2 m2 hst2_inv hag2 htr2
          (by dsimp [st2, st1]; omega) (hrel2.trans hrel) (Or.inr (Or.inl rfl))
          (by simp) (fun _ => ⟨by dsimp [st2, st1]; omega, hoom2_0, ?_⟩)
          (fun hoom0 hE _ => ?_) (fun h => absurd h hne_end) hm2
        · exact (hconfl hok_f).resolve_left (fun h => h hoom2_0)
        · have hok_t := (hws0 (hws_e hoom0 hE)).1; rw [hok_f] at hok_t; cases hok_t
    · have hpr_eq : st.propagated = st.trail_end := by c0_bound
      refine hret_st 0#64 st ml hst_inv hag htr hfuel_le hrel (Or.inl rfl)
        (fun _ => ⟨hpr_eq, hoom_pres⟩) (by simp) (fun hoom0 hE _ => ?_)
        (fun h => ⟨rfl, hnoop h⟩) hml
      obtain ⟨hwv_eq, hvals_eq, hte_eq, _, hsum⟩ := hempty hoom0 hE
      exact ⟨rfl, hvals_eq, hte_eq, by omega, hwv_eq, hoom_pres hoom0, by omega⟩
  · intro L hL; pp_steps
    exact hL s.fuel.toNat () m ⟨s, rfl, hinv, .refl _ _, .refl s, Nat.le_refl _, rfl,
      fun h => h, fun _ _ => ⟨rfl, rfl, rfl, Nat.le_refl _, by omega⟩, fun _ => rfl, hm⟩

/-! ## 2. Head-only stepper, framing mask, and `plain_prop_lit` `Func.wp` proof -/

private theorem wp_head_eq {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {e1 e2 : Expr Val Cont rs} (h : e1 = e2) (hk : wp Γ Q X e2 m) :
    wp Γ Q X e1 m := h ▸ hk

private theorem wp_let_head {Γ : Env} {rs sig ts : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {c : OpCode sig ts} {args : Tup (Arg Val) sig} {k : Tup Val ts → Expr Val Cont rs}
    {r : Tup Val ts}
    (hr : ∀ P, P r → c.wp (vals args) P)
    (hk : wp Γ Q X (k r) m) :
    wp Γ Q X (.let_ (Op.mk c args) k) m := hr _ hk

private theorem wp_blocks_here {Γ : Env} {rs ts : List Ty} {sig : List (List Ty)}
    {Q : Post rs} {X : XPost} {m : Mem 64}
    {b : Tup Val ts → Expr Val Cont rs} {bs : Blocks Val Cont rs sig} {xs : Tup Val ts}
    (h : wp Γ Q X (b xs) m) :
    wp Γ Q X (Blocks.get (Blocks.cons b bs) .here xs) m := h

private theorem wp_ret_head {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {xs : Tup (Arg Val) rs} (h : Q (vals xs) m) : wp Γ Q X (.ret xs) m := h

private theorem wp_jump_head {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {J : Cont ts} {xs : Tup (Arg Val) ts} (h : J (vals xs) m) : wp Γ Q X (.jump J xs) m := h

section FastLet
variable {Γ : Env} {rs : List Ty} {n : Nat} {Q : Post rs} {X : XPost} {m : Mem 64}
private theorem wp_let_add_b {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (va + vb, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.add (.bits n)) (a, b, ())) k) m := by cases ha; cases hb; exact hk
private theorem wp_let_sub_b {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (va - vb, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.sub (.bits n)) (a, b, ())) k) m := by cases ha; cases hb; exact hk
private theorem wp_let_mul_b {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (va * vb, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.mul (.bits n)) (a, b, ())) k) m := by cases ha; cases hb; exact hk
private theorem wp_let_and_b {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (va &&& vb, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.and (.bits n)) (a, b, ())) k) m := by cases ha; cases hb; exact hk
private theorem wp_let_or_b {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (va ||| vb, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.or (.bits n)) (a, b, ())) k) m := by cases ha; cases hb; exact hk
private theorem wp_let_xor_b {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (va ^^^ vb, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.xor (.bits n)) (a, b, ())) k) m := by cases ha; cases hb; exact hk
private theorem wp_let_eq_b {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (va == vb, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .eq (.bits n)) (a, b, ())) k) m := by
  cases ha; cases hb
  simpa only [wp, Op.wp, OpCode.wp, vals, liftCmp, evalBits_eq_beq, Ty.hasFloat,
    Bool.false_eq_true, ite_false] using hk
private theorem wp_let_ne_b {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (va != vb, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .ne (.bits n)) (a, b, ())) k) m := by
  cases ha; cases hb
  simpa only [wp, Op.wp, OpCode.wp, vals, liftCmp, evalBits_ne_bne, Ty.hasFloat,
    Bool.false_eq_true, ite_false] using hk
private theorem wp_let_ult_b {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (va.ult vb, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .ult (.bits n)) (a, b, ())) k) m := by cases ha; cases hb; exact hk
private theorem wp_let_ule_b {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (va.ule vb, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .ule (.bits n)) (a, b, ())) k) m := by cases ha; cases hb; exact hk
private theorem wp_let_ugt_b {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (vb.ult va, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .ugt (.bits n)) (a, b, ())) k) m := by cases ha; cases hb; exact hk
private theorem wp_let_uge_b {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (vb.ule va, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .uge (.bits n)) (a, b, ())) k) m := by cases ha; cases hb; exact hk
private theorem wp_let_slt_b {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (va.slt vb, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .slt (.bits n)) (a, b, ())) k) m := by cases ha; cases hb; exact hk
private theorem wp_let_sle_b {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (va.sle vb, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .sle (.bits n)) (a, b, ())) k) m := by cases ha; cases hb; exact hk
private theorem wp_let_sgt_b {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (vb.slt va, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .sgt (.bits n)) (a, b, ())) k) m := by cases ha; cases hb; exact hk
private theorem wp_let_sge_b {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (vb.sle va, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .sge (.bits n)) (a, b, ())) k) m := by cases ha; cases hb; exact hk
private theorem wp_let_zext32_64 {a : Arg Val i32} {va : BitVec 32} {k} (ha : a.val = va)
    (hk : wp Γ Q X (k (va.setWidth 64, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.zext 32 64) (a, ())) k) m := by cases ha; exact ⟨by decide, hk⟩
private theorem wp_let_sext8_32 {a : Arg Val i8} {va : BitVec 8} {k} (ha : a.val = va)
    (hk : wp Γ Q X (k (va.signExtend 32, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.sext 8 32) (a, ())) k) m := by cases ha; exact ⟨by decide, hk⟩
private theorem wp_let_trunc64_32 {a : Arg Val i64} {va : BitVec 64} {k} (ha : a.val = va)
    (hk : wp Γ Q X (k (va.setWidth 32, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.trunc 64 32) (a, ())) k) m := by cases ha; exact ⟨by decide, hk⟩
private theorem wp_let_shl64_1 {a b : Arg Val i64} {va : BitVec 64} {k} (ha : a.val = va)
    (hb : b.val = 1#64) (hk : wp Γ Q X (k (va <<< (1 : Nat), ())) m) :
    wp Γ Q X (.let_ (Op.mk (.shl i64) (a, b, ())) k) m := by
  cases ha
  simpa only [wp, Op.wp, OpCode.wp, vals, lift2, hb, BitVec.reduceToNat, Nat.reduceMod,
    Ty.hasFloat, Bool.false_eq_true, ite_false] using hk
end FastLet

local macro "pp_head_let" : tactic =>
  `(tactic| (
    apply wp_let_head
    · intro P hP; try dsimp (config := { zeta := false }) only
      simp only [OpCode.wp, OpCode.wp_cmp, OpCode.wp_select, OpCode.eq, OpCode.ne, OpCode.ult,
        OpCode.ule, OpCode.ugt, OpCode.uge, OpCode.slt, OpCode.sle, OpCode.sgt, OpCode.sge,
        vals_nil, vals_cons, Arg.val_var, Arg.val_imm, Ty.hasFloat_vec, Ty.hasFloat, Ty.isFloatTree,
        evalBits_eq_beq, evalBits_ne_bne, evalBits_ult_eq, evalBits_ule_eq, evalBits_ugt_eq,
        evalBits_uge_eq, evalBits_slt_eq, evalBits_sle_eq, evalBits_sgt_eq, evalBits_sge_eq,
        evalBool_eq_beq, evalBool_ne_bne, evalBool_ult_eq, evalBool_ule_eq, evalBool_ugt_eq,
        evalBool_uge_eq, evalBool_slt_eq, evalBool_sle_eq, evalBool_sgt_eq, evalBool_sge_eq,
        lift1, lift2, lift3, liftCmp, cast_eq, ite_true, ite_false, Bool.false_eq_true,
        Bool.true_eq_false, BitVec.reduceSignExtend, BitVec.reduceSetWidth, BitVec.reduceAdd,
        BitVec.reduceMul, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceDiv]
      try refine ⟨by decide, ?_⟩
      exact hP))

private theorem bv64_shl1_nat (x : BitVec 32) :
    (x.setWidth 64 <<< (1 : Nat)).toNat = 2 * x.toNat := bv64_shl1_u32 x

private theorem bv64_shl1_add1_nat (x : BitVec 32) :
    ((x.setWidth 64 <<< (1 : Nat)) + (1 : BitVec 64)).toNat = 2 * x.toNat + 1 := by
  have hx := x.isLt
  rw [bv64_add1_toNat (by rw [bv64_shl1_nat]; omega), bv64_shl1_nat]

local elab "pp_head_steps" : tactic => do
  let binOps : Array (Lean.Name × Lean.Name) := #[
    (``OpCode.add, ``wp_let_add_b), (``OpCode.sub, ``wp_let_sub_b), (``OpCode.mul, ``wp_let_mul_b),
    (``OpCode.and, ``wp_let_and_b), (``OpCode.or, ``wp_let_or_b), (``OpCode.xor, ``wp_let_xor_b),
    (``OpCode.eq, ``wp_let_eq_b), (``CmpOp.eq, ``wp_let_eq_b), (``OpCode.ne, ``wp_let_ne_b),
    (``CmpOp.ne, ``wp_let_ne_b), (``OpCode.ult, ``wp_let_ult_b), (``CmpOp.ult, ``wp_let_ult_b),
    (``OpCode.ule, ``wp_let_ule_b), (``CmpOp.ule, ``wp_let_ule_b), (``OpCode.ugt, ``wp_let_ugt_b),
    (``CmpOp.ugt, ``wp_let_ugt_b), (``OpCode.uge, ``wp_let_uge_b), (``CmpOp.uge, ``wp_let_uge_b),
    (``OpCode.slt, ``wp_let_slt_b), (``CmpOp.slt, ``wp_let_slt_b), (``OpCode.sle, ``wp_let_sle_b),
    (``CmpOp.sle, ``wp_let_sle_b), (``OpCode.sgt, ``wp_let_sgt_b), (``CmpOp.sgt, ``wp_let_sgt_b),
    (``OpCode.sge, ``wp_let_sge_b), (``CmpOp.sge, ``wp_let_sge_b)]
  let unOps : Array (Lean.Name × Lean.Name) := #[
    (``OpCode.zext, ``wp_let_zext32_64), (``OpCode.sext, ``wp_let_sext8_32),
    (``OpCode.trunc, ``wp_let_trunc64_32)]
  let clearSet : Array Lean.Name := #[
    ``Exists, ``Std.ExtHashMap.sep, ``PlainMem, ``PlainCoreInv, ``PropLitInv, ``SplitWatchesInv,
    ``AgreesExcept, ``TrailExt, ``PlainState.LengthsOk, ``PlainHeur.LengthsOk]
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
    ``load_arena_len, ``load_arena_search_ticks, ``load_arena_wusable, ``load_arena_values,
    ``load_arena_watch_vec, ``load_arena_arena_ptr, ``load_arena_watch_stk, ``load_arena_mv]
  let hdrStoreLems : Array Lean.Name := #[
    ``store_arena_search_ticks, ``store_arena_wusable, ``store_arena_oom, ``store_arena_confl_type,
    ``store_arena_confl_ref, ``store_arena_confl_lit0, ``store_arena_confl_lit1]
  let pickLems (isLoad : Bool) (ty : Lean.Expr) : Array Lean.Name :=
    if (ty.find? (·.isConstOf ``PlainCfg.pWstk)).isSome then
      if isLoad then #[``c0_load_arena_wstk] else #[``c0_store_arena_wstk]
    else if (ty.find? (·.isConstOf ``PlainCfg.pArena)).isSome then
      if isLoad then #[``c0_load_arena_arena] else #[``c0_store_arena_arena]
    else if (ty.find? (·.isConstOf ``PlainCfg.pVals)).isSome then
      if isLoad then #[``c0_load_arena_vals] else #[]
    else if (ty.find? (·.isConstOf ``PlainCfg.pWvec)).isSome then
      if isLoad then #[``c0_load_arena_wvec] else #[``c0_store_arena_wvec]
    else if isLoad then hdrLoadLems else hdrStoreLems
  let solveMem (isLoad : Bool) (hmv : Lean.MVarId) : Lean.Elab.Tactic.TacticM Unit := do
    Lean.Elab.Tactic.setGoals [hmv]
    Lean.Elab.Tactic.evalTactic
      (← `(tactic| (try simp only [LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm]);
        (try dsimp (config := { zeta := false }) only)))
    let hmv ← Lean.Elab.Tactic.getMainGoal
    let lems := pickLems isLoad (← Lean.instantiateMVars (← hmv.getType))
    let mut solved := false
    for nm in lems do
      let s ← Lean.saveState
      let ok ← try
        let sub ← Lean.Meta.withReducible <| hmv.apply (← Lean.Meta.mkConstWithFreshMVarLevels nm)
        let mut allOk := true
        for g' in sub do
          if !allOk then break
          if (← Lean.instantiateMVars (← g'.getType)).isAppOf ``Std.ExtHashMap.sep then
            Lean.Elab.Tactic.setGoals [g']
            Lean.Meta.withReducible <|
              Lean.Elab.Tactic.evalTactic (← `(tactic| first | assumption | c0_frame))
            if !(← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then allOk := false
        for g' in sub do
          if !allOk || (← g'.isAssigned) then continue
          if ← Lean.Meta.isProp (← g'.getType) then
            Lean.Elab.Tactic.setGoals [g']
            Lean.Elab.Tactic.evalTactic (← `(tactic| first | rfl | assumption | decide | skip))
            if (← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then continue
            let g' ← Lean.Elab.Tactic.getMainGoal
            let toClear ← g'.withContext do
              let mut ids : Array Lean.FVarId := #[]
              for d in (← Lean.getLCtx).decls do
                let some d := d | continue
                if d.isAuxDecl || d.isLet then continue
                if ← Lean.Meta.isProp d.type then
                  let ty := d.type.consumeMData
                  let isBig := ty.isForall && !ty.bindingBody!.consumeMData.isConstOf ``False
                  if isBig || (ty.getAppFn.constName?.any (clearSet.contains ·)) then
                    ids := ids.push d.fvarId
              pure ids
            let g' ← g'.tryClearMany toClear
            Lean.Elab.Tactic.setGoals [g']
            Lean.Elab.Tactic.evalTactic (← `(tactic|
              ((try dsimp (config := { zeta := false }) only)
               (try simp only [List.length_set])
               first | assumption | rfl | decide | omega
                     | (simp only [bv_c0_zext32_64, bv32_xor_1, bv64_shl1_nat,
                          bv64_shl1_add1_nat, BitVec.toNat_add, ← BitVec.ofNat_eq_ofNat,
                          BitVec.toNat_ofNat, Nat.reduceMod, BitVec.reduceToNat]; omega))))
            if !(← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then allOk := false
        for g' in sub do if !(← g'.isAssigned) then allOk := false
        pure allOk
      catch _ => pure false
      if ok then solved := true; break else s.restore
    if !solved then throwError "pp_head_steps: solveMem failed on {← hmv.getType}"
  let headBetaWp (g : Lean.MVarId) : Lean.Elab.Tactic.TacticM Lean.MVarId :=
    g.withContext do
      let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData.headBeta
      if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 then
        let e' := (ty.getArg! 4).consumeMData.headBeta.consumeMData
        if e' == ty.getArg! 4 then return g
        let mvar ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar
          (Lean.mkAppN ty.getAppFn (ty.getAppArgs.set! 4 e'))
        g.assign (← Lean.Meta.mkAppM ``wp_head_eq #[← Lean.Meta.mkEqRefl e', mvar])
        return mvar.mvarId!
      return g
  let mut todo ← Lean.Elab.Tactic.getGoals
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
      Lean.Elab.Tactic.setGoals [g]
      Lean.Elab.Tactic.evalTactic (← `(tactic| apply wp_blocks_here))
      todo := (← Lean.Elab.Tactic.getGoals) ++ todo
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
          let s ← Lean.saveState
          try
            let [hk] ← g.apply (← Lean.Meta.mkAppOptM nm xs) | s.restore; return none
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
        else if c == some ``OpCode.shl && !ia && r.isAppOf ``Prod.mk && r.getAppNumArgs ≥ 4 then
          let b := r.getArg! 2
          let some (vb, _) := argVal b | return none
          applyPf ``wp_let_shl64_1 #[some gΓ, some grs, some gQ, some gX, some gm, some a, some b,
            some va, some gk, some (← Lean.Meta.mkEqRefl va), some (← Lean.Meta.mkEqRefl vb)]
        else return none
      if let some hk := fastGoal? then
        todo := hk :: todo
      else
        Lean.Elab.Tactic.setGoals [g]
        Lean.Elab.Tactic.evalTactic (← `(tactic| pp_head_let))
        todo := (← Lean.Elab.Tactic.getGoals) ++ todo
    else if fn? == some ``LeanQbe.T.Expr.load then
      let gs ← g.withContext <|
        g.apply (← Lean.Meta.mkConstWithFreshMVarLevels ``LeanQbe.T.wp_load_of)
      let [hl, hk] := gs.take 2 | throwError "pp_head_steps: bad load"
      solveMem true hl
      todo := hk :: todo
    else if fn? == some ``LeanQbe.T.Expr.store then
      let gs ← g.withContext <|
        g.apply (← Lean.Meta.mkConstWithFreshMVarLevels ``LeanQbe.T.wp_store_sep)
      let [hs, hk] := gs.take 2 | throwError "pp_head_steps: bad store"
      solveMem false hs
      Lean.Elab.Tactic.setGoals [hk]
      let mId := Lean.mkIdent `m
      let hmId := Lean.mkIdent `hm
      Lean.Elab.Tactic.evalTactic (← `(tactic| intro $mId:ident $hmId:ident))
      Lean.Elab.Tactic.evalTactic (← `(tactic| try simp only [LeanQbe.T.Arg.val_var,
        LeanQbe.T.Arg.val_imm, Std.ExtHashMap.sep_emp] at $hmId:ident))
      Lean.Elab.Tactic.evalTactic
        (← `(tactic| try dsimp (config := { zeta := false }) only at $hmId:ident))
      if let .fvar mId0 := m0 then
        Lean.Elab.Tactic.withMainContext do
          for d in (← Lean.getLCtx).decls.toArray.reverse do
            let some d := d | continue
            let t ← Lean.instantiateMVars d.type
            if t.isAppOf ``Std.ExtHashMap.sep && t.appArg! == m0 then
              try Lean.Elab.Tactic.liftMetaTactic1 fun g => some <$> g.clear d.fvarId
              catch _ => pure ()
          try Lean.Elab.Tactic.liftMetaTactic1 fun g => some <$> g.clear mId0
          catch _ => pure ()
      todo := (← Lean.Elab.Tactic.getGoals) ++ todo
    else if fn? == some ``LeanQbe.T.Expr.jnz then
      Lean.Elab.Tactic.setGoals [g]
      let hc := Lean.mkIdent `hc
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        refine wp_jnz_of (fun $hc:ident => ?_) (fun $hc:ident => ?_) <;> (
          try simp only [Arg.val_var, Arg.val_imm] at $hc:ident
          c0_cond $hc
          try (first | exact ($hc).elim | exact absurd rfl $hc | exact $hc rfl
                     | exact absurd trivial $hc))))
      todo := (← Lean.Elab.Tactic.getGoals) ++ todo
    else if fn? == some ``LeanQbe.T.Expr.ret then
      Lean.Elab.Tactic.setGoals [g]
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        (apply wp_ret_head; simp only [vals_nil, vals_cons, Arg.val_var, Arg.val_imm])))
      done := (← Lean.Elab.Tactic.getGoals).reverse ++ done
    else if fn? == some ``LeanQbe.T.Expr.jump then
      Lean.Elab.Tactic.setGoals [g]
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        (apply wp_jump_head; simp only [vals_nil, vals_cons, Arg.val_var, Arg.val_imm])))
      done := (← Lean.Elab.Tactic.getGoals).reverse ++ done
    else
      done := g :: done
  Lean.Elab.Tactic.setGoals done.reverse

private theorem propLit_finish {c : PlainCfg} {F0 : CNF Nat} {s st : PlainState}
    {not_lit : BitVec 32} {off_v p_v q_v end_v q_c : BitVec 64} {confl_v : Bool}
    {wstk_c wstk_k : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {idx1 : Nat}
    (hpi : PropLitInv c F0 s st not_lit.toNat off_v.toNat q_v.toNat p_v.toNat end_v.toNat)
    (hnot_lt : not_lit.toNat < 2 * c.mv) (hwl3 : wstk_k.length = c.wcap)
    (hpc_eq : q_c.toNat = q_v.toNat + (end_v.toNat - p_v.toNat))
    (hidx1 : idx1 = 2 * not_lit.toNat + 1)
    (hpre : ∀ k, off_v.toNat ≤ k → k < q_v.toNat → wstk_c[k]? = st.wstk[k]?)
    (hsuf : ∀ k < end_v.toNat - p_v.toNat, wstk_c[q_v.toNat + k]? = st.wstk[p_v.toNat + k]?)
    (hout : ∀ k, (k < off_v.toNat ∨ end_v.toNat ≤ k) → wstk_c[k]? = st.wstk[k]?)
    (hkeep : ∀ i, (i < q_v.toNat + (end_v.toNat - p_v.toNat) ∨ end_v.toNat ≤ i) →
      wstk_k[i]? = wstk_c[i]?)
    (hcf_f : confl_v = false → st.oom = 0#64) (hcf_t : confl_v = true → PropLitConfl c F0 st)
    (hm : (PlainMem c { st with
        wstk := wstk_k, wvec := st.wvec.set idx1 ((q_c - off_v).setWidth 32),
        wusable := st.wusable + (end_v - q_c) } ⋆ R) m) :
    let st_fin : PlainState :=
      { st with
        wstk := wstk_k, wusable := st.wusable + (end_v - q_c),
        wvec := st.wvec.set (2 * not_lit.toNat + 1)
          (BitVec.ofNat 32 (q_v.toNat + (end_v.toNat - p_v.toNat) - off_v.toNat)) }
    PlainCoreInv c F0 st_fin ∧ AgreesExcept (propLitMask s.heur) s st_fin ∧ TrailExt s st_fin ∧
    st_fin.heur.rel_trigger = s.heur.rel_trigger ∧
    ((!confl_v) = false → PropLitConfl c F0 st_fin) ∧ ((!confl_v) = true → st_fin.oom = 0#64) ∧
    (PlainMem c st_fin ⋆ R) m := by
  intro st_fin
  have hq_ge := hpi.sw.q_ge; have hq_le := hpi.sw.q_le_p; have hp_le := hpi.sw.p_le_end
  have ⟨_, hwlen_le⟩ := hpi.end_lt_wcap hnot_lt; have hwvec_len := hpi.len.wvec_len
  have hset_wvec : (q_c - off_v).setWidth 32 =
      BitVec.ofNat 32 (q_v.toNat + (end_v.toNat - p_v.toNat) - off_v.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, bv64_sub_toNat (by omega), hpc_eq, BitVec.toNat_ofNat]
  have hwat_fin := hpi.sw.finish hnot_lt hwvec_len c.hwcap hwlen_le
    (fun k h1 h2 => (hkeep k (Or.inl (by omega))).trans (hpre k h1 h2))
    (fun k hk => (hkeep _ (Or.inl (by omega))).trans (hsuf k hk))
    (fun k hk => (hkeep k (hk.elim (fun _ => Or.inl (by omega)) Or.inr)).trans (hout k hk))
    (wu' := st.wusable + (end_v - q_c))
  have hlen_fin : st_fin.LengthsOk c :=
    { hpi.len with wvec_len := by simp [st_fin, hwvec_len], wstk_len_arr := hwl3 }
  refine ⟨plainCoreInv_of_nw
      (plainCoreInv_nw_congr hpi.nw hlen_fin rfl rfl rfl rfl rfl rfl rfl rfl rfl) hlen_fin hwat_fin,
    hpi.ag.update (fun t => { t with wstk := wstk_k, wvec := st_fin.wvec, wusable := _ }),
    hpi.tr.congr rfl rfl rfl, hpi.rel,
    fun hnf => (hcf_t (by cases confl_v <;> simp at hnf ⊢)).congr rfl rfl rfl rfl rfl rfl rfl rfl,
    fun hnt => hcf_f (by cases confl_v <;> simp at hnt ⊢), ?_⟩
  subst hidx1; dsimp only [st_fin]; rw [← hset_wvec]; exact hm

private theorem propLit_b1_swap {c : PlainCfg} {F0 : CNF Nat} {s st1 : PlainState}
    {not_lit other cref repl : BitVec 32} {off_v p_v q_v end_v : BitVec 64}
    {r i4 ir : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hpi1 : PropLitInv c F0 s st1 not_lit.toNat off_v.toNat q_v.toNat (p_v.toNat + 2) end_v.toNat)
    (hcr_lt : cref.toNat < st1.arena_len) (hcr_ref1 : cref.toNat ∈ arenaClauseRefs st1)
    (hcr_fit : cref.toNat + 3 + arenaClauseSize st1 cref.toNat ≤ st1.arena_len)
    (har4 : st1.arena[cref.toNat + 4]? = some not_lit)
    (hr2 : 2 ≤ r) (hr_lt : r < arenaClauseSize st1 cref.toNat)
    (hi4 : i4 = cref.toNat + 4) (hir : ir = cref.toNat + 3 + r)
    (hrepl_def : repl = (st1.arena.set (cref.toNat + 1) (BitVec.ofNat 32 r))[ir]'(by
      have := hpi1.len.arena_len_arr; have := hpi1.len.arena_len_le; simp; omega))
    (hcand : (st1.arena[cref.toNat + 3 + r]?.getD 0#32).toNat < 2 * c.mv ∧
      ((st1.vals[(st1.arena[cref.toNat + 3 + r]?.getD 0#32).toNat]?.getD 0#8).signExtend 32).slt
        0#32 = false)
    (hm : (PlainMem c { st1 with arena := (((st1.arena.set (cref.toNat + 1)
        (BitVec.ofNat 32 r)).set i4 repl).set ir not_lit) } ⋆ R) m) :
    let st3 : PlainState := { st1 with arena := ((st1.arena.set (cref.toNat + 1)
      (BitVec.ofNat 32 r)).set (cref.toNat + 4) repl).set (cref.toNat + 3 + r) not_lit }
    st3.LengthsOk c ∧ PlainCoreInv c F0 (withEmptyWatches c st3) ∧
    SplitWatchesInv c F0 st3 not_lit.toNat off_v.toNat q_v.toNat (p_v.toNat + 2) end_v.toNat ∧
    cref.toNat ∈ arenaClauseRefs st3 ∧
    arenaClauseSize st3 cref.toNat = arenaClauseSize st1 cref.toNat ∧
    repl.toNat < 2 * c.mv ∧ repl.toNat ≠ not_lit.toNat ∧
    (other &&& 0x7FFFFFFF#32) ≠ 0xFFFFFFFF#32 ∧ cref ≠ 0xFFFFFFFF#32 ∧ (PlainMem c st3 ⋆ R) m := by
  intro st3; subst hi4; subst hir
  let st2 : PlainState := { st1 with arena := st1.arena.set (cref.toNat + 1) (BitVec.ofNat 32 r) }
  have har := c.harena; unfold dimacsBound at har
  have haren1 := hpi1.len.arena_len_arr; have halen1_le := hpi1.len.arena_len_le
  have ⟨hnw2, href2, hcl2⟩ :=
    arena_setSrch_preserves_nw hpi1.nw hcr_ref1 (srch := BitVec.ofNat 32 r)
  have hlen2 : st2.LengthsOk c := { hpi1.len with arena_len_arr := by simp [st2, haren1] }
  have hsw2 := hpi1.sw.with_nonwatch (s' := st2) rfl rfl rfl href2
  have hcr_ref2 : cref.toNat ∈ arenaClauseRefs st2 := href2.symm ▸ hcr_ref1
  have hcsz2 : arenaClauseSize st2 cref.toNat = arenaClauseSize st1 cref.toNat :=
    (hcl2 cref.toNat hcr_ref1).1
  have hrepl_get : st1.arena[cref.toNat + 3 + r]?.getD 0#32 = repl := by
    have h1 : st2.arena[cref.toNat + 3 + r]? = some repl := by
      rw [hrepl_def]; exact List.getElem?_eq_getElem (by simp [st2]; omega)
    rw [← List.getElem?_set_ne (by omega : cref.toNat + 1 ≠ cref.toNat + 3 + r),
      show (st1.arena.set (cref.toNat + 1) (BitVec.ofNat 32 r))[cref.toNat + 3 + r]? =
        some repl from h1, Option.getD_some]
  obtain ⟨hrepl_lt, hrepl_slt⟩ := hcand; rw [hrepl_get] at hrepl_lt hrepl_slt
  have hrepl_ne_not : repl.toNat ≠ not_lit.toNat := fun heq =>
    i8_vals_ne_of_slt_false hpi1.not_f (heq ▸ hrepl_slt) rfl
  have hst2_ar4 : st2.arena[cref.toNat + 3 + 1]'(by simp [st2]; omega) = not_lit :=
    Option.some.inj ((List.getElem?_eq_getElem (by simp [st2]; omega)).symm.trans
      ((List.getElem?_set_ne (by omega)).trans har4))
  have ⟨hnw3, href3, hcl3⟩ := arena_swapLits_preserves_nw hnw2 hcr_ref2 (k1 := 1) (k2 := r)
    (by change 1 < arenaClauseSize st2 cref.toNat; omega)
    (by change r < arenaClauseSize st2 cref.toNat; omega)
  have hst3_sw : st3 = { st2 with
    arena := (st2.arena.set (cref.toNat + 3 + 1)
        (st2.arena[cref.toNat + 3 + r]'(by simp [st2]; omega))).set
      (cref.toNat + 3 + r) (st2.arena[cref.toNat + 3 + 1]'(by simp [st2]; omega)) } := by
    simp only [st3, st2, hst2_ar4, ← hrepl_def]
  rw [← hst3_sw] at hnw3 href3 hcl3
  have hw0_ne_ff : (other &&& 0x7FFFFFFF#32) ≠ 0xFFFFFFFF#32 := fun hff => by
    have h := bv32_mask7f_flag0 other; rw [hff] at h; exact absurd h (by decide)
  have hcr_ne_ff : cref ≠ 0xFFFFFFFF#32 := fun hff => by
    rw [hff] at hcr_lt; have : (0xFFFFFFFF#32).toNat = 0xFFFFFFFF := (by decide); omega
  exact ⟨{ hlen2 with arena_len_arr := by simp [st3, haren1] }, hnw3,
    hsw2.with_nonwatch (s' := st3) rfl rfl rfl href3, href3.symm ▸ hcr_ref2,
    (hcl3 cref.toNat hcr_ref2).1.trans hcsz2, hrepl_lt, hrepl_ne_not, hw0_ne_ff, hcr_ne_ff, hm⟩

private theorem propLit_b1_after_push {c : PlainCfg} {F0 : CNF Nat} {st3 st4 : PlainState}
    {lit other cref repl : BitVec 32} {off_v p_v q_v end_v : BitVec 64} {pok : Bool} {idx0 : Nat}
    (hidx0 : idx0 = 2 * (lit ^^^ 1#32).toNat) (hnot_lt : (lit ^^^ 1#32).toNat < 2 * c.mv)
    (hlen4 : st4.LengthsOk c) (hlay4 : WatchStackLayout c st4)
    (hsw3 : SplitWatchesInv c F0 st3 (lit ^^^ 1#32).toNat off_v.toNat q_v.toNat
      (p_v.toNat + 2) end_v.toNat)
    (hrefs : arenaClauseRefs st4 = arenaClauseRefs st3)
    (hrepl_lt : repl.toNat < 2 * c.mv) (hrepl_ne : repl.toNat ≠ (lit ^^^ 1#32).toNat)
    (hcr_lt : cref.toNat < 0x80000000) (hcr_ref3 : cref.toNat ∈ arenaClauseRefs st3)
    (hp2_nat : (p_v + (1 : BitVec 64) + (1 : BitVec 64)).toNat = p_v.toNat + 2)
    (hq_le_p : q_v.toNat ≤ p_v.toNat)
    (hpres_o : ∀ l < 2 * c.mv, l ≠ repl.toNat → watchSize st4 l = watchSize st3 l ∧
      ∀ k < watchSize st3 l, st4.wstk[watchOff st4 l + k]? = st3.wstk[watchOff st3 l + k]?)
    (hpok_t : pok = true → watchSize st4 repl.toNat = watchSize st3 repl.toNat + 2 ∧
      (∀ k < watchSize st3 repl.toNat,
        st4.wstk[watchOff st4 repl.toNat + k]? = st3.wstk[watchOff st3 repl.toNat + k]?) ∧
      st4.wstk[watchOff st4 repl.toNat + watchSize st3 repl.toNat]? =
        some (other &&& 0x7FFFFFFF#32) ∧
      st4.wstk[watchOff st4 repl.toNat + watchSize st3 repl.toNat + 1]? = some cref)
    (hpok_f : pok = false → watchSize st4 repl.toNat = watchSize st3 repl.toNat ∧
      ∀ k < watchSize st3 repl.toNat,
        st4.wstk[watchOff st4 repl.toNat + k]? = st3.wstk[watchOff st3 repl.toNat + k]?) :
    let off4_v : BitVec 64 := (st4.wvec[idx0]'(by have := hlen4.wvec_len; omega)).setWidth 64
    let q4_v := off4_v + (q_v - off_v)
    watchOff st4 (lit ^^^ 1#32).toNat + (end_v.toNat - off_v.toNat) ≤ st4.wlen ∧
    off4_v.toNat = watchOff st4 (lit ^^^ 1#32).toNat ∧
    (off4_v + (p_v + (1 : BitVec 64) + (1 : BitVec 64) - off_v)).toNat =
      watchOff st4 (lit ^^^ 1#32).toNat + (p_v.toNat + 2 - off_v.toNat) ∧
    q4_v.toNat = watchOff st4 (lit ^^^ 1#32).toNat + (q_v.toNat - off_v.toNat) ∧
    (off4_v + (end_v - off_v)).toNat =
      watchOff st4 (lit ^^^ 1#32).toNat + (end_v.toNat - off_v.toNat) ∧
    (q4_v + (1 : BitVec 64)).toNat = q4_v.toNat + 1 ∧
    (q4_v + (2 : BitVec 64)).toNat = q4_v.toNat + 2 ∧
    SplitWatchesInv c F0 st4 (lit ^^^ 1#32).toNat off4_v.toNat q4_v.toNat
      (off4_v + (p_v + (1 : BitVec 64) + (1 : BitVec 64) - off_v)).toNat
      (off4_v + (end_v - off_v)).toNat := by
  intro off4_v q4_v
  have hwc := c.hwcap; unfold dimacsBound at hwc
  have hwlen4 := hlen4.wlen_le; have hwvec4 := hlen4.wvec_len
  have hq_ge := hsw3.q_ge; have hp_le := hsw3.p_le_end
  have hsw4 := hsw3.after_push (st' := st4) hnot_lt hrepl_lt hrepl_ne hrefs hlay4
    (bv32_mask7f_flag0 other) hcr_lt hcr_ref3 hpres_o hpok_t hpok_f
  have hoff4_bd : watchOff st4 (lit ^^^ 1#32).toNat + (end_v.toNat - off_v.toNat) ≤ st4.wlen := by
    have hb := hlay4.bounds (lit ^^^ 1#32).toNat hnot_lt; have hsz4 := hsw4.sz_eq
    have hsz_e : watchSize st4 (lit ^^^ 1#32).toNat = end_v.toNat - off_v.toNat := by omega
    rw [hsz_e] at hb; exact hb
  have hoff4_nat : off4_v.toNat = watchOff st4 (lit ^^^ 1#32).toNat := by
    dsimp only [off4_v]; rw [bv_c0_zext32_64]; unfold watchOff
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact congrArg BitVec.toNat (by congr 1)
  have hp4_nat : (off4_v + (p_v + (1 : BitVec 64) + (1 : BitVec 64) - off_v)).toNat =
      watchOff st4 (lit ^^^ 1#32).toNat + (p_v.toNat + 2 - off_v.toNat) := by
    rw [bv64_add_toNat (by rw [bv64_sub_toNat (by omega), hp2_nat]; omega),
      hoff4_nat, bv64_sub_toNat (by omega), hp2_nat]
  have hq4_nat : q4_v.toNat = watchOff st4 (lit ^^^ 1#32).toNat + (q_v.toNat - off_v.toNat) := by
    dsimp only [q4_v]
    rw [bv64_add_toNat (by rw [bv64_sub_toNat (by omega)]; omega),
      hoff4_nat, bv64_sub_toNat (by omega)]
  have hend4_nat : (off4_v + (end_v - off_v)).toNat =
      watchOff st4 (lit ^^^ 1#32).toNat + (end_v.toNat - off_v.toNat) := by
    rw [bv64_add_toNat (by rw [bv64_sub_toNat (by omega)]; omega),
      hoff4_nat, bv64_sub_toNat (by omega)]
  exact ⟨hoff4_bd, hoff4_nat, hp4_nat, hq4_nat, hend4_nat,
    bv64_add1_toNat (by omega), bv64_add2_toNat (by omega),
    by rw [hoff4_nat, hq4_nat, hp4_nat, hend4_nat]; exact hsw4⟩

private theorem propLit_b1_oom {c : PlainCfg} {F0 : CNF Nat} {s st1 st4 : PlainState}
    {not_lit w0 cref repl : BitVec 32} {off_v p_v q_v end_v off4_v : BitVec 64}
    {r i4 ir q4_1 : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hpi1 : PropLitInv c F0 s st1 not_lit.toNat off_v.toNat q_v.toNat (p_v.toNat + 2) end_v.toNat)
    (hlen4 : st4.LengthsOk c) (hnw4 : PlainCoreInv c F0 (withEmptyWatches c st4))
    (hsw4' : SplitWatchesInv c F0 st4 not_lit.toNat off4_v.toNat (off4_v + (q_v - off_v)).toNat
      (off4_v + (p_v + (1 : BitVec 64) + (1 : BitVec 64) - off_v)).toNat
      (off4_v + (end_v - off_v)).toNat)
    (har_eq : st4.arena = ((st1.arena.set (cref.toNat + 1) (BitVec.ofNat 32 r)).set
      (cref.toNat + 4) repl).set (cref.toNat + 3 + r) not_lit)
    (hal_eq : st4.arena_len = st1.arena_len) (hrel4 : st4.heur.rel_trigger = s.heur.rel_trigger)
    (hag4 : AgreesExcept (propLitMask s.heur) s st4) (htr4 : TrailExt s st4)
    (hnot4 : st4.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8)
    (hnot_lt : not_lit.toNat < 2 * c.mv) (hq_le_p : q_v.toNat ≤ p_v.toNat)
    (hcr_lt : cref.toNat < 0x80000000) (hcr_ref3 : cref.toNat ∈ arenaClauseRefs st4)
    (hflag : (w0 &&& 0x80000000#32) = 0#32)
    (hcr_fit : cref.toNat + 3 + arenaClauseSize st4 cref.toNat ≤ st1.arena_len)
    (hr2 : 2 ≤ r) (hr_lt : r < arenaClauseSize st4 cref.toNat)
    (hi4 : i4 = cref.toNat + 4) (hir : ir = cref.toNat + 3 + r)
    (hq4_nat : (off4_v + (q_v - off_v)).toNat =
      watchOff st4 not_lit.toNat + (q_v.toNat - off_v.toNat))
    (hp4_nat : (off4_v + (p_v + (1 : BitVec 64) + (1 : BitVec 64) - off_v)).toNat =
      watchOff st4 not_lit.toNat + (p_v.toNat + 2 - off_v.toNat))
    (hend4_nat : (off4_v + (end_v - off_v)).toNat =
      watchOff st4 not_lit.toNat + (end_v.toNat - off_v.toNat))
    (hq4_1 : q4_1 = (off4_v + (q_v - off_v)).toNat + 1)
    (hq4_2 : (off4_v + (q_v - off_v) + (2 : BitVec 64)).toNat = (off4_v + (q_v - off_v)).toNat + 2)
    (hm : (PlainMem c { st4 with
        arena := (st4.arena.set i4 not_lit).set ir repl,
        wstk := (st4.wstk.set (off4_v + (q_v - off_v)).toNat w0).set q4_1 cref,
        oom := (1 : BitVec 64) } ⋆ R) m) :
    let q4_v := off4_v + (q_v - off_v)
    let st6 : PlainState := { st4 with
      arena := (st4.arena.set (cref.toNat + 4) not_lit).set (cref.toNat + 3 + r) repl,
      wstk := (st4.wstk.set q4_v.toNat w0).set (q4_v.toNat + 1) cref, oom := 1#64 }
    PropLitInv c F0 s st6 not_lit.toNat off4_v.toNat (q4_v + (2 : BitVec 64)).toNat
      (off4_v + (p_v + (1 : BitVec 64) + (1 : BitVec 64) - off_v)).toNat
      (off4_v + (end_v - off_v)).toNat ∧ (PlainMem c st6 ⋆ R) m := by
  intro q4_v st6
  have haren4 := hlen4.arena_len_arr; have halen4 := hlen4.arena_len_le
  have hwstk4 := hlen4.wstk_len_arr; have hwlen4 := hlen4.wlen_le
  have hb4 := hsw4'.layout.bounds not_lit.toNat hnot_lt
  have hoff4 := hsw4'.off_eq; have hsz4 := hsw4'.sz_eq
  have hq4_ge := hsw4'.q_ge; have hq4_le := hsw4'.q_le_p; have hp4_le := hsw4'.p_le_end
  have hq_ge := hpi1.sw.q_ge; have hq_le := hpi1.sw.q_le_p; have hp_le := hpi1.sw.p_le_end
  have hst4_ar4 : st4.arena[cref.toNat + 3 + 1]'(by omega) = repl := by
    have h1 : st4.arena[cref.toNat + 4]'(by omega) = repl := by
      simp only [har_eq]; rw [List.getElem_set_ne (by omega), List.getElem_set_self]
    exact h1
  have hst4_arr : st4.arena[cref.toNat + 3 + r]'(by omega) = not_lit := by
    simp only [har_eq]; rw [List.getElem_set_self]
  have ⟨hnw5, href5, _⟩ := arena_swapLits_preserves_nw hnw4 hcr_ref3 (k1 := 1) (k2 := r)
    (by omega) (by omega)
  let st5 : PlainState :=
    { st4 with arena := (st4.arena.set (cref.toNat + 4) not_lit).set (cref.toNat + 3 + r) repl }
  have hst5_sw : st5 = { st4 with
    arena := (st4.arena.set (cref.toNat + 3 + 1) (st4.arena[cref.toNat + 3 + r]'(by omega))).set
      (cref.toNat + 3 + r) (st4.arena[cref.toNat + 3 + 1]'(by omega)) } := by
    simp only [st5, hst4_ar4, hst4_arr]
  rw [← hst5_sw] at hnw5 href5
  have hcr_ref5 : cref.toNat ∈ arenaClauseRefs st5 := href5.symm ▸ hcr_ref3
  have hsw5 := hsw4'.with_nonwatch (s' := st5) rfl rfl rfl href5
  have hq4_e : q4_v.toNat = watchOff st4 not_lit.toNat + (q_v.toNat - off_v.toNat) := hq4_nat
  have hp4_split : (off4_v + (p_v + (1 : BitVec 64) + (1 : BitVec 64) - off_v)).toNat =
      (watchOff st4 not_lit.toNat + (p_v.toNat - off_v.toNat)) + 2 := by omega
  have hsw5_w := (by rwa [hp4_split] at hsw5 :
      SplitWatchesInv c F0 st5 not_lit.toNat off4_v.toNat q4_v.toNat
        ((watchOff st4 not_lit.toNat + (p_v.toNat - off_v.toNat)) + 2)
        (off4_v + (end_v - off_v)).toNat).write_large hnot_lt (by omega)
    (by simp [st5]; omega) (by simp [st5]; omega) hflag hcr_lt hcr_ref5
  have hlen6 : st6.LengthsOk c :=
    { hlen4 with arena_len_arr := by simp [st6, haren4], wstk_len_arr := by simp [st6, hwstk4] }
  refine ⟨{ len := hlen6
            nw := plainCoreInv_nw_congr hnw5 hlen6 rfl rfl rfl rfl rfl rfl rfl rfl rfl
            sw := by rw [hq4_2, hp4_split]; exact hsw5_w.with_nonwatch rfl rfl rfl rfl
            ag := hag4.update (fun t =>
              { t with arena := st6.arena, wstk := st6.wstk, oom := 1#64 })
            tr := htr4.congr rfl rfl rfl, rel := hrel4, not_f := hnot4 }, ?_⟩
  subst hi4; subst hir; subst hq4_1; exact hm

private theorem propLit_js3_swap {c : PlainCfg} {F0 : CNF Nat} {s st_t : PlainState}
    {not_lit cref l1 : BitVec 32} {off_v p_v q_v end_v : BitVec 64}
    {i3 i4 : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hlen_t : st_t.LengthsOk c) (hnw_t : PlainCoreInv c F0 (withEmptyWatches c st_t))
    (hsw_t : SplitWatchesInv c F0 st_t not_lit.toNat off_v.toNat q_v.toNat
      (p_v.toNat + 2) end_v.toNat)
    (hag_t : AgreesExcept (propLitMask s.heur) s st_t) (htr : TrailExt s st_t)
    (hrel : st_t.heur.rel_trigger = s.heur.rel_trigger)
    (hnot_f : st_t.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8)
    (hcr_ref : cref.toNat ∈ arenaClauseRefs st_t) (hng_t : arenaClauseGarb st_t cref.toNat = false)
    (hcsz3 : 3 ≤ arenaClauseSize st_t cref.toNat)
    (hcr_fit : cref.toNat + 3 + arenaClauseSize st_t cref.toNat ≤ st_t.arena_len)
    (hi3 : i3 = cref.toNat + 3) (hi4 : i4 = cref.toNat + 4)
    (hl0_eq : st_t.arena[cref.toNat + 3]'(by
      have := hlen_t.arena_len_arr; have := hlen_t.arena_len_le; omega) = not_lit)
    (hl1_eq : st_t.arena[cref.toNat + 4]'(by
      have := hlen_t.arena_len_arr; have := hlen_t.arena_len_le; omega) = l1)
    (hm : (PlainMem c { st_t with
        arena := (st_t.arena.set i3 l1).set i4 not_lit } ⋆ R) m) :
    let st1 : PlainState :=
      { st_t with arena := (st_t.arena.set (cref.toNat + 3) l1).set (cref.toNat + 4) not_lit }
    PropLitInv c F0 s st1 not_lit.toNat off_v.toNat q_v.toNat (p_v.toNat + 2) end_v.toNat ∧
    cref.toNat ∈ arenaClauseRefs st1 ∧ arenaClauseGarb st1 cref.toNat = false ∧
    arenaClauseSize st1 cref.toNat = arenaClauseSize st_t cref.toNat ∧
    st1.arena[cref.toNat + 3]? = some l1 ∧ st1.arena[cref.toNat + 4]? = some not_lit ∧
    (PlainMem c st1 ⋆ R) m := by
  intro st1
  have haren := hlen_t.arena_len_arr; have halen := hlen_t.arena_len_le
  have ⟨hnw1, href1, hcl1⟩ := arena_swapLits_preserves_nw hnw_t hcr_ref (k1 := 0) (k2 := 1)
    (by omega) (by omega)
  have hst1_sw : st1 = { st_t with
    arena := (st_t.arena.set (cref.toNat + 3 + 0) (st_t.arena[cref.toNat + 3 + 1]'(by omega))).set
      (cref.toNat + 3 + 1) (st_t.arena[cref.toNat + 3 + 0]'(by omega)) } := by
    simp only [st1, hl0_eq, hl1_eq]
  rw [← hst1_sw] at hnw1 href1 hcl1
  have hlen1 : st1.LengthsOk c := { hlen_t with arena_len_arr := by simp [st1, haren] }
  refine ⟨{ len := hlen1, nw := hnw1, sw := hsw_t.with_nonwatch rfl rfl rfl href1,
            ag := hag_t.update (fun t => { t with arena := st1.arena }),
            tr := htr.congr rfl rfl rfl, rel := hrel, not_f := hnot_f },
    href1.symm ▸ hcr_ref, (hcl1 cref.toNat hcr_ref).2.1.trans hng_t, (hcl1 cref.toNat hcr_ref).1,
    by simp [st1, List.getElem?_set_ne (by omega : cref.toNat + 4 ≠ cref.toNat + 3),
         List.getElem?_set_self (show cref.toNat + 3 < st_t.arena.length by omega)],
    by rw [List.getElem?_set_self (by simp; omega)], ?_⟩
  subst hi3; subst hi4; exact hm

private theorem propLit_measure_lt {a b c d : Nat} (h1 : a ≤ b) (h2 : b + 2 ≤ c) :
    (d + (c - a)) - (d + (b + 2 - a)) < c - b := by omega

theorem plain_prop_lit_wp (Γ : Env)
    (hFind : ∀ args m Q X, plainFindReplSpec args m Q X →
      Γ "plain_find_repl" [i64, i64] [i64] args m Q X)
    (hPush : ∀ args m Q X, plainWatchPushSpec args m Q X →
      Γ "plain_watch_push" [i64, i32, i32, i32, i32] [.bool] args m Q X)
    (hAssign : ∀ args m Q X, plainAssignSpec args m Q X →
      Γ "plain_assign" [i64, i32, i32] [] args m Q X) :
    ∀ args m Q X, plainPropLitSpec args m Q X →
      Func.wp Γ plain_prop_lit_body args m Q X := by
  rintro ⟨h, lit, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hoom0, hm, hQ⟩
  have hmv := c.hmv; have har := c.harena; have hwc := c.hwcap
  unfold dimacsBound at hmv har hwc
  have hlen0 := hinv.lengths
  let not_lit : BitVec 32 := lit ^^^ 1#32
  have hret_st : ∀ (ok : Bool) (st : PlainState) (ml : Mem 64),
      PlainCoreInv c F0 st → AgreesExcept (propLitMask s.heur) s st → TrailExt s st →
      st.heur.rel_trigger = s.heur.rel_trigger →
      (ok = false → PropLitConfl c F0 st) →
      (watchSize s not_lit.toNat = 0 → ok = true ∧ st = s) →
      (ok = true → st.oom = 0#64) →
      (PlainMem c st ⋆ R) ml → Q (ok, ()) ml := by
    intro ok st ml hst hag htr hrel hcf hws0 hok_oom hml
    have hst_eq := propLit_eq_upd hag
    have hst' := hst; rw [hst_eq] at hst' hml
    refine hQ ok st.vals st.lvl st.rsns st.trl st.trail_pos st.trail_end st.unflushed
      st.wvec st.arena st.wstk st.wlen st.wusable st.confl_type st.confl_ref
      st.confl_lit0 st.confl_lit1 st.oom st.heur ml hst' htr.te_ge hrel
      htr.trl_pref htr.lvl_pres htr.new_lvl ?_ ?_ hok_oom hml
    · intro hf; unfold PropLitConfl at hcf; simpa only [← hst_eq] using hcf hf
    · intro hz; obtain ⟨ht, heq⟩ := hws0 hz; exact ⟨ht, hst_eq ▸ heq⟩
  have hret_noop : Q (true, ()) m :=
    hret_st true s m hinv (.refl _ _) (.refl _) rfl (by simp)
      (fun _ => ⟨rfl, rfl⟩) (fun _ => hoom0) hm
  have hvl0 := hlen0.vals_len; have hwv0 := hlen0.wvec_len
  unfold Func.wp plain_prop_lit_body
  pp_head_steps
  · exact hret_noop
  · exact hret_noop
  · exact hret_noop
  · have hnot_xor : not_lit.toNat = lit.toNat ^^^ 1 := bv32_xor_1 lit
    have hnot_lt : not_lit.toNat < 2 * c.mv := by
      have h1 : ¬ 2 * (c.mv % 2 ^ 64) % 2 ^ 64 ≤ lit.toNat ^^^ 1 := by assumption
      rw [Nat.mod_eq_of_lt (by omega : c.mv < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : 2 * c.mv < 2 ^ 64)] at h1; omega
    have hnot_f0 : s.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8 := by
      have hsge : (0#32).sle ((s.vals[not_lit.toNat]'(by omega)).signExtend 32) = false := by
        have h2 : (0#32).sle ((s.vals[lit.toNat ^^^ 1]'(by omega)).signExtend 32) = false := by
          assumption
        simpa only [hnot_xor] using h2
      rw [bv32_sle0_eq_not_slt0, Bool.not_eq_false'] at hsge
      have hget : s.vals[not_lit.toNat]?.getD 0#8 = s.vals[not_lit.toNat]'(by omega) := by
        simp [List.getElem?_eq_getElem (show not_lit.toNat < s.vals.length by omega)]
      rw [hget]; exact (i8_vals_slt0 (by rw [← hget]; exact hinv.vals_domain _ hnot_lt)).mp hsge
    have hidx0 : ((lit ^^^ (1 : BitVec 32)).setWidth 64 <<< (1 : BitVec 64)).toNat =
        2 * not_lit.toNat := bv64_shl1_u32 not_lit
    have hidx1 : (((lit ^^^ (1 : BitVec 32)).setWidth 64 <<< (1 : BitVec 64)) +
        (1 : BitVec 64)).toNat = 2 * not_lit.toNat + 1 := by
      rw [bv64_add1_toNat (by rw [hidx0]; omega), hidx0]
    have hoff0_eq : (s.wvec[((lit ^^^ (1 : BitVec 32)).setWidth 64 <<<
        (1 : BitVec 64)).toNat]'(by omega)).toNat = watchOff s not_lit.toNat := by
      unfold watchOff; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      exact congrArg BitVec.toNat (by congr 1)
    have hsz0_eq : (s.wvec[(((lit ^^^ (1 : BitVec 32)).setWidth 64 <<< (1 : BitVec 64)) +
        (1 : BitVec 64)).toNat]'(by omega)).toNat = watchSize s not_lit.toNat := by
      unfold watchSize; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      exact congrArg BitVec.toNat (by congr 1)
    have hsz0_pos : 0 < watchSize s not_lit.toNat := by
      rw [← hsz0_eq]
      have h1 : (2 * (lit.toNat ^^^ 1) + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 =
          (((lit ^^^ (1 : BitVec 32)).setWidth 64 <<< (1 : BitVec 64)) +
            (1 : BitVec 64)).toNat := by
        rw [hidx1, ← hnot_xor]; change (2 * not_lit.toNat + 1) % 2 ^ 64 = _
        exact Nat.mod_eq_of_lt (by omega)
      have heq_w : s.wvec[(2 * (lit.toNat ^^^ 1) + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(
            by omega) = s.wvec[(((lit ^^^ (1 : BitVec 32)).setWidth 64 <<< (1 : BitVec 64)) +
            (1 : BitVec 64)).toNat]'(by omega) := by congr 1
      have hne0 : (s.wvec[(((lit ^^^ (1 : BitVec 32)).setWidth 64 <<< (1 : BitVec 64)) +
          (1 : BitVec 64)).toNat]'(by omega)).setWidth 64 ≠ 0#64 := fun heq => hc (by
        change (s.wvec[(2 * (lit.toNat ^^^ 1) + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(
          by omega)).setWidth 64 = 0#64
        rw [heq_w]; exact heq)
      exact Nat.pos_of_ne_zero fun h0 =>
        hne0 (BitVec.eq_of_toNat_eq (by rw [bv_c0_zext32_64, h0]; rfl))
    have hws0_ne : watchSize s not_lit.toNat ≠ 0 := by omega
    clear hc; clear hc
    let st0 : PlainState :=
      { s with heur := { s.heur with search_ticks := s.heur.search_ticks + 1#64 } }
    have hlen_st0 : st0.LengthsOk c := hlen0.with_heur (hlen0.heur_ok.with_ticks _)
    have hpi0 : PropLitInv c F0 s st0 not_lit.toNat (watchOff s not_lit.toNat)
        (watchOff s not_lit.toNat) (watchOff s not_lit.toNat)
        (watchOff s not_lit.toNat + watchSize s not_lit.toNat) :=
      { len := hlen_st0
        nw := plainCoreInv_nw_congr (plainCoreInv_to_nw hinv) hlen_st0
          rfl rfl rfl rfl rfl rfl rfl rfl rfl
        sw := (SplitWatchesInv.init hnot_lt hinv.watches hsz0_pos).with_nonwatch rfl rfl rfl rfl
        ag := (AgreesExcept.refl (propLitMask s.heur) s).update
          (fun t => { t with heur := st0.heur })
        tr := (TrailExt.refl s).congr rfl rfl rfl, rel := rfl, not_f := hnot_f0 }
    have hbin_rsn := bv32_bin_rsn_props (x := not_lit) (by omega)
    refine wp_loop_break_group
      (fun (off_v, p_v, q_v, end_v, confl_v, ()) mb => ∃ st : PlainState,
        PropLitInv c F0 s st not_lit.toNat off_v.toNat q_v.toNat p_v.toNat end_v.toNat ∧
        (confl_v = false → st.oom = 0#64) ∧ (confl_v = true → PropLitConfl c F0 st) ∧
        (PlainMem c st ⋆ R) mb)
      (fun rem (off_v, p_v, q_v, end_v, ()) ml => ∃ st : PlainState,
        rem = end_v.toNat - p_v.toNat ∧
        PropLitInv c F0 s st not_lit.toNat off_v.toNat q_v.toNat p_v.toNat end_v.toNat ∧
        st.oom = 0#64 ∧ (PlainMem c st ⋆ R) ml) ?_ ?_ ?_
    · -- Post-loop break/exit join `B`: Loop 2 (tail copy) -> Loop 3 (sentinel fill) -> store -> ret
      rintro _ ⟨off_v, p_v, q_v, end_v, confl_v, ⟨⟩⟩ mb ⟨st, hpi, hcf_f, hcf_t, hmb⟩
      clear hc hret_noop hvl0 hwv0 hoff0_eq hsz0_eq hsz0_pos hpi0 hlen_st0 st0 hnot_f0 hm hinv hlen0
        hoom0 hbin_rsn hidx0
      have ⟨hend_le, hwlen_le⟩ := hpi.end_lt_wcap hnot_lt
      have hq_ge := hpi.sw.q_ge; have hq_le := hpi.sw.q_le_p; have hp_le := hpi.sw.p_le_end
      have hwstk_len := hpi.len.wstk_len_arr; have hwvec_len := hpi.len.wvec_len
      let q_fin : Nat := q_v.toNat + (end_v.toNat - p_v.toNat)
      -- Loop 2: `while (p < end) { wstk[q] = wstk[p]; q++; p++; }`
      refine wp_loop_inv
        (fun (p_c, q_c, ()) m2 => ∃ wstk_c : List (BitVec 32),
          wstk_c.length = c.wcap ∧ p_v.toNat ≤ p_c.toNat ∧ p_c.toNat ≤ end_v.toNat ∧
          q_c.toNat = q_v.toNat + (p_c.toNat - p_v.toNat) ∧
          (∀ k, off_v.toNat ≤ k → k < q_v.toNat → wstk_c[k]? = st.wstk[k]?) ∧
          (∀ k < p_c.toNat - p_v.toNat, wstk_c[q_v.toNat + k]? = st.wstk[p_v.toNat + k]?) ∧
          (∀ k, p_c.toNat ≤ k → k < end_v.toNat → wstk_c[k]? = st.wstk[k]?) ∧
          (∀ k, (k < off_v.toNat ∨ end_v.toNat ≤ k) → wstk_c[k]? = st.wstk[k]?) ∧
          (PlainMem c { st with wstk := wstk_c } ⋆ R) m2)
        (fun (p_c, _, ()) _ => end_v.toNat - p_c.toNat)
        (fun L2 hL2 => by
          pp_head_steps
          exact hL2 (p_v, q_v, ()) mb ⟨st.wstk, hwstk_len, Nat.le_refl _, hp_le, by omega,
            fun _ _ _ => rfl, fun _ hk => by omega, fun _ _ _ => rfl, fun _ _ => rfl, hmb⟩)
        (fun L2 (p_c, q_c, ()) m2 ⟨wstk_c, hwl2, hp_ge, hp_le2, hqc_eq,
            hpre, hsuf, hrem, hout, hm2⟩ ih2 => ?_)
      pp_head_steps
      · have hp_lt : p_c.toNat < end_v.toNat := hc
        have hstep := propLit_loop2_step hq_ge hq_le hp_ge hp_lt (by omega) (by omega)
          hpre hsuf hrem hout
        have hpc_add : (p_c + (1 : BitVec 64)).toNat = p_c.toNat + 1 := bv64_add1_toNat (by omega)
        have hqc_add : (q_c + (1 : BitVec 64)).toNat =
            q_v.toNat + ((p_c + (1 : BitVec 64)).toNat - p_v.toNat) := by
          rw [bv64_add1_toNat (by omega), hpc_add]; omega
        refine ih2 (p_c + (1 : BitVec 64), q_c + (1 : BitVec 64), ()) m (by dsimp only; omega)
          ⟨wstk_c.set q_c.toNat (wstk_c[p_c.toNat]'(by omega)), by simp [hwl2],
            by omega, by omega, hqc_add, ?_, ?_, ?_, ?_, hm⟩
        · simpa only [← hqc_eq] using hstep.1
        · rw [hpc_add]; simpa only [← hqc_eq] using hstep.2.1
        · rw [hpc_add]; simpa only [← hqc_eq] using hstep.2.2.1
        · simpa only [← hqc_eq] using hstep.2.2.2
      · have hpc_eq : p_c.toNat = end_v.toNat := by omega
        have hqfin_eq : q_c.toNat = q_fin := by dsimp [q_fin]; omega
        -- Loop 3: `k = q; while (k < end) { wstk[k] = 0xFFFFFFFFu; k++; }`
        refine wp_loop_inv
          (fun (k_c, ()) m3 => ∃ wstk_k : List (BitVec 32),
            wstk_k.length = c.wcap ∧ q_fin ≤ k_c.toNat ∧ k_c.toNat ≤ end_v.toNat ∧
            (∀ i, (i < q_fin ∨ end_v.toNat ≤ i) → wstk_k[i]? = wstk_c[i]?) ∧
            (PlainMem c { st with wstk := wstk_k } ⋆ R) m3)
          (fun (k_c, ()) _ => end_v.toNat - k_c.toNat)
          (fun L3 hL3 => by
            pp_head_steps
            exact hL3 (q_c, ()) m2 ⟨wstk_c, hwl2, by omega, by omega,
              fun _ _ => rfl, hm2⟩)
          (fun L3 (k_c, ()) m3 ⟨wstk_k, hwl3, hk_ge, hk_le, hkeep, hm3⟩ ih3 => ?_)
        pp_head_steps
        · have hk_lt : k_c.toNat < end_v.toNat := hc
          have hk_add : (k_c + 1#64).toNat = k_c.toNat + 1 := bv64_add1_toNat (by omega)
          refine ih3 (k_c + 1#64, ()) m (by dsimp only; omega)
            ⟨wstk_k.set k_c.toNat 0xFFFFFFFF#32, by simp [hwl3], by omega, by omega,
              propLit_loop3_step hk_ge hk_lt hkeep, hm⟩
        · have ⟨hcore_fin, hag_fin, htr_fin, hrel_fin, hcf_fin, hoom_fin, hm_fin⟩ :=
            propLit_finish hpi hnot_lt hwl3 hqfin_eq hidx1 hpre (fun k hk => hsuf k (by omega))
              hout hkeep hcf_f hcf_t hm
          exact hret_st (!confl_v) _ m hcore_fin hag_fin htr_fin hrel_fin hcf_fin
            (fun hz => absurd hz hws0_ne) hoom_fin hm_fin
    · -- Main loop body `L`: `while (p < end)`
      rintro B L rem ⟨off_v, p_v, q_v, end_v, ⟨⟩⟩ ml hB ih ⟨st, rfl, hpi, hoom_st, hml⟩
      clear hc hret_noop hvl0 hwv0 hoff0_eq hsz0_eq hsz0_pos hpi0 hlen_st0 st0 hnot_f0 hm hinv hlen0
        hoom0 hbin_rsn hidx1 hws0_ne hret_st hQ
      have ⟨hend_le, hwlen_le⟩ := hpi.end_lt_wcap hnot_lt
      have hq_ge := hpi.sw.q_ge; have hq_le := hpi.sw.q_le_p; have hp_le := hpi.sw.p_le_end
      have hwstk_len := hpi.len.wstk_len_arr; have hvals_len := hpi.len.vals_len
      have haren_len := hpi.len.arena_len_arr; have halen_le := hpi.len.arena_len_le
      have hwvec_len := hpi.len.wvec_len
      have h1_64 : ((1 : BitVec 64)).toNat = 1 := rfl
      have hp1_pre : (p_v + (1 : BitVec 64)).toNat = p_v.toNat + 1 := bv64_add1_toNat (by omega)
      pp_head_steps
      · -- Binary watch, `other >= nlits` (dead!)
        have hp_lt : p_v.toNat < end_v.toNat := by assumption
        have hw0_get : st.wstk[p_v.toNat]? = some (st.wstk[p_v.toNat]'(by omega)) :=
          List.getElem?_eq_getElem (by omega)
        have hflag : (st.wstk[p_v.toNat]'(by omega) &&& 0x80000000#32) ≠ 0#32 := by assumption
        have ⟨hother_lt, _, _⟩ := watchSlice_inv_bin hpi.sw.rem_slice (by omega) hw0_get hflag
        have hge : 2 * (c.mv % 2 ^ 64) % 2 ^ 64 ≤
            (st.wstk[p_v.toNat]'(by omega) &&& 0x7FFFFFFF#32).toNat := hc
        rw [Nat.mod_eq_of_lt (by omega : c.mv < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : 2 * c.mv < 2 ^ 64)] at hge
        omega
      · -- Binary watch, `ov > 0`: keep watch & continue
        have hp_lt : p_v.toNat < end_v.toNat := by assumption
        have hw0_get : st.wstk[p_v.toNat]? = some (st.wstk[p_v.toNat]'(by omega)) :=
          List.getElem?_eq_getElem (by omega)
        have hflag : (st.wstk[p_v.toNat]'(by omega) &&& 0x80000000#32) ≠ 0#32 := by assumption
        have ⟨hother_lt, hent, hrem1⟩ :=
          watchSlice_inv_bin hpi.sw.rem_slice (by omega) hw0_get hflag
        have hsw1 := (hpi.sw.advance_rem (p' := p_v.toNat + 1) (by omega) (by omega)
          (by simpa [Nat.sub_sub] using hrem1)).write_bin hnot_lt hq_le (by omega)
          hflag hother_lt hent
        let st1 : PlainState :=
          { st with wstk := st.wstk.set q_v.toNat (st.wstk[p_v.toNat]'(by omega)) }
        have hlen1 : st1.LengthsOk c := { hpi.len with wstk_len_arr := by simp [st1, hwstk_len] }
        have hp1 : (p_v + 1#64).toNat = p_v.toNat + 1 := bv64_add1_toNat (by omega)
        have hq1 : (q_v + 1#64).toNat = q_v.toNat + 1 := bv64_add1_toNat (by omega)
        refine ih (end_v.toNat - (p_v + 1#64).toNat) (off_v, p_v + 1#64, q_v + 1#64, end_v, ()) m
          (by omega) ⟨st1, rfl, ?_, hoom_st, hm⟩
        exact
          { len := hlen1
            nw := plainCoreInv_nw_congr hpi.nw hlen1 rfl rfl rfl rfl rfl rfl rfl rfl rfl
            sw := by rwa [hp1, hq1]
            ag := hpi.ag.update (fun t => { t with wstk := st1.wstk })
            tr := hpi.tr.congr rfl rfl rfl, rel := hpi.rel, not_f := hpi.not_f }
      · -- Binary watch, `ov < 0`: record binary conflict & break
        have hp_lt : p_v.toNat < end_v.toNat := by assumption
        have hw0_get : st.wstk[p_v.toNat]? = some (st.wstk[p_v.toNat]'(by omega)) :=
          List.getElem?_eq_getElem (by omega)
        have hflag : (st.wstk[p_v.toNat]'(by omega) &&& 0x80000000#32) ≠ 0#32 := by assumption
        have ⟨hother_lt, hent, hrem1⟩ :=
          watchSlice_inv_bin hpi.sw.rem_slice (by omega) hw0_get hflag
        have hsw1 := (hpi.sw.advance_rem (p' := p_v.toNat + 1) (by omega) (by omega)
          (by simpa [Nat.sub_sub] using hrem1)).write_bin hnot_lt hq_le (by omega)
          hflag hother_lt hent
        have hov_f := propLit_vals_neg hpi.nw hother_lt (by omega) hc
        have ⟨hpi_c, hcf_c⟩ := propLit_bin_confl hpi hsw1 hnot_lt hother_lt hent hov_f
          (bv64_add1_toNat (by omega)) (bv64_add1_toNat (by omega))
        exact hB (off_v, p_v + 1#64, q_v + 1#64, end_v, true, ()) m
          ⟨_, hpi_c, by simp, fun _ => hcf_c, hm⟩
      · -- Binary watch, `ov == 0`: `plain_assign(h, other, bin_rsn)` & continue
        have hp_lt : p_v.toNat < end_v.toNat := by assumption
        have hw0_get : st.wstk[p_v.toNat]? = some (st.wstk[p_v.toNat]'(by omega)) :=
          List.getElem?_eq_getElem (by omega)
        have hflag : (st.wstk[p_v.toNat]'(by omega) &&& 0x80000000#32) ≠ 0#32 := by assumption
        have ⟨hother_lt, hent, hrem1⟩ :=
          watchSlice_inv_bin hpi.sw.rem_slice (by omega) hw0_get hflag
        have hsw1 := (hpi.sw.advance_rem (p' := p_v.toNat + 1) (by omega) (by omega)
          (by simpa [Nat.sub_sub] using hrem1)).write_bin hnot_lt hq_le (by omega)
          hflag hother_lt hent
        let w0 := st.wstk[p_v.toNat]'(by omega)
        let other := w0 &&& 0x7FFFFFFF#32
        have hother_lt' : other.toNat < 2 * c.mv := hother_lt
        let st1 : PlainState := { st with wstk := st.wstk.set q_v.toNat w0 }
        have hlen1 : st1.LengthsOk c := { hpi.len with wstk_len_arr := by simp [st1, hwstk_len] }
        have hnw1 : PlainCoreInv c F0 (withEmptyWatches c st1) :=
          plainCoreInv_nw_congr hpi.nw hlen1 rfl rfl rfl rfl rfl rfl rfl rfl rfl
        have hov_un : st1.vals[other.toNat]?.getD 0#8 = 0#8 :=
          propLit_vals_un hnw1 hother_lt' (by simp [st1]; omega) (by assumption) hc
        have hte_lt : st1.trail_end < c.mv := hnw1.trail_end_lt_of_unassigned hother_lt' hov_un
        have hcl_lt32 : st1.cur_level < 2 ^ 32 := by
          have h1 : st1.cur_level ≤ st1.trail_end := hnw1.cur_level_le
          have h2 : st1.trail_end ≤ c.mv := hlen1.trail_end_le; omega
        have hng_guard :
            ¬ (c.mv ≤ (st.wstk[p_v.toNat]'(by omega) &&& (2147483647 : BitVec 32)).toNat / 2 ∨
              c.mv ≤ st1.trail_end) := by
          change ¬ (c.mv ≤ other.toNat / 2 ∨ c.mv ≤ st1.trail_end); omega
        c0_call hAssign
        refine ⟨c, st1, R, rfl, hlen1, hcl_lt32, hm, ?_⟩
        simp only [hng_guard, ↓reduceIte]
        intro phases' m_as hph hlen_as hm_as
        let st2 : PlainState :=
          { st1 with
            vals := (st1.vals.set other.toNat 1#8).set (other.toNat ^^^ 1) 0xFF#8
            lvl := st1.lvl.set (other.toNat / 2) (BitVec.ofNat 32 st1.cur_level)
            rsns := st1.rsns.set (other.toNat / 2)
              (if st1.cur_level = 0 then 0xFFFFFFFF#32
               else (not_lit &&& 0x7FFFFFFF#32) ||| 0x80000000#32)
            trl := st1.trl.set st1.trail_end other
            trail_pos := st1.trail_pos.set (other.toNat / 2) (BitVec.ofNat 32 st1.trail_end)
            trail_end := st1.trail_end + 1
            unflushed := if st1.cur_level = 0 then st1.unflushed + 1#64 else st1.unflushed
            heur := { st1.heur with phases := phases' } }
        have ⟨hnw2, hnot_f2, htr12⟩ := bin_assign_nw_step hnw1 hnot_lt hother_lt' hph hov_un
          hpi.not_f hent
          (unfl' := if st1.cur_level = 0 then st1.unflushed + 1#64 else st1.unflushed)
        have hcl_eq : st1.cur_level = s.cur_level := hpi.ag.get PlainState.cur_level
        have hp1 : (p_v + 1#64).toNat = p_v.toNat + 1 := bv64_add1_toNat (by omega)
        have hq1 : (q_v + 1#64).toNat = q_v.toNat + 1 := bv64_add1_toNat (by omega)
        pp_head_steps
        refine ih (end_v.toNat - (p_v + 1#64).toNat) (off_v, p_v + 1#64, q_v + 1#64, end_v, ()) m_as
          (by omega) ⟨st2, rfl, ?_, hoom_st, hm_as⟩
        exact
          { len := hlen_as, nw := hnw2
            sw := by rw [hp1, hq1]; exact hsw1.with_nonwatch rfl rfl rfl rfl
            ag := hpi.ag.update (fun t => { t with
              vals := st2.vals, lvl := st2.lvl, rsns := st2.rsns, trl := st2.trl,
              trail_pos := st2.trail_pos, trail_end := st2.trail_end, unflushed := st2.unflushed,
              wstk := st1.wstk, heur := st2.heur })
            tr := (hpi.tr.congr (s2 := st1) rfl rfl rfl).trans htr12 hcl_eq
            rel := hpi.rel, not_f := hnot_f2 }
      · -- Large watch, `p + 1 >= end` (dead!)
        have hp_lt : p_v.toNat < end_v.toNat := by assumption
        have hw0_get : st.wstk[p_v.toNat]? = some (st.wstk[p_v.toNat]'(by omega)) :=
          List.getElem?_eq_getElem (by omega)
        have hflag : (st.wstk[p_v.toNat]'(by omega) &&& 0x80000000#32) = 0#32 := by assumption
        have ⟨h2le, _⟩ := watchSlice_inv_large hpi.sw.rem_slice (by omega) hw0_get hflag
        have hge : end_v.toNat ≤ (p_v.toNat + 1) % 2 ^ 64 := hc
        rw [Nat.mod_eq_of_lt (by omega : p_v.toNat + 1 < 2 ^ 64)] at hge
        omega
      · -- Large watch, `p + 1 < end`: `cref = wstk[p + 1]`, `p2 = p + 2`, then join `Js_2`
        have hp_lt : p_v.toNat < end_v.toNat := by assumption
        have hw0_get : st.wstk[p_v.toNat]? = some (st.wstk[p_v.toNat]'(by omega)) :=
          List.getElem?_eq_getElem (by omega)
        have hflag : (st.wstk[p_v.toNat]'(by omega) &&& 0x80000000#32) = 0#32 := by assumption
        have ⟨h2le, cref0, hcr_get, hcr_lt, hcr_ref, hrem2⟩ :=
          watchSlice_inv_large hpi.sw.rem_slice (by omega) hw0_get hflag
        have hp1_nat : (p_v + (1 : BitVec 64)).toNat = p_v.toNat + 1 := bv64_add1_toNat (by omega)
        have hp2_nat : (p_v + (1 : BitVec 64) + (1 : BitVec 64)).toNat = p_v.toNat + 2 := by
          rw [bv64_add1_toNat (by omega), hp1_nat]
        have hq1_nat : (q_v + (1 : BitVec 64)).toNat = q_v.toNat + 1 := bv64_add1_toNat (by omega)
        have hq2_nat : (q_v + (2 : BitVec 64)).toNat = q_v.toNat + 2 := bv64_add2_toNat (by omega)
        have hcr_idx_lt : (p_v + (1 : BitVec 64)).toNat < st.wstk.length := by omega
        have hcr_eq : st.wstk[(p_v + (1 : BitVec 64)).toNat]'hcr_idx_lt = cref0 := by
          have h1 : st.wstk[p_v.toNat + 1]? =
              some (st.wstk[(p_v + (1 : BitVec 64)).toNat]'hcr_idx_lt) := by
            rw [← hp1_nat]; exact List.getElem?_eq_getElem hcr_idx_lt
          exact Option.some.inj (h1.symm.trans hcr_get)
        generalize hcr_gen : st.wstk[(p_v + (1 : BitVec 64)).toNat]'hcr_idx_lt = cref at hcr_eq ⊢
        generalize hw0_gen : st.wstk[p_v.toNat]'(by omega) = w0 at hflag ⊢
        rw [← hcr_eq] at hcr_lt hcr_ref
        have hsw_drop : SplitWatchesInv c F0 st not_lit.toNat off_v.toNat q_v.toNat
            (p_v.toNat + 2) end_v.toNat :=
          hpi.sw.advance_rem (p' := p_v.toNat + 2) (by omega) (by omega)
            (by simpa [Nat.sub_sub] using hrem2)
        -- Join `Js_2`: blocking literal did NOT satisfy clause
        refine wp_join_group (fun () m1 => m1 = ml) ?_ ?_
        · rintro _ ⟨⟩ m1 rfl
          have hcr_wf := hpi.nw.arena.refs_wf cref.toNat hcr_ref
          have hcr3_le : cref.toNat + 3 ≤ st.arena_len := hcr_wf.1
          have hcsz3 : 3 ≤ arenaClauseSize st cref.toNat := hcr_wf.2.1
          have hcr_next : cref.toNat + 3 + arenaClauseSize st cref.toNat ≤
              arenaNextOff st.arena st.arena_len cref.toNat := hcr_wf.2.2.1
          have hnext_le : arenaNextOff st.arena st.arena_len cref.toNat ≤ st.arena_len :=
            hcr_wf.2.2.2.1
          have hcr_fit : cref.toNat + 3 + arenaClauseSize st cref.toNat ≤ st.arena_len := by omega
          have hcr64 : (cref.setWidth 64).toNat = cref.toNat := bv_c0_zext32_64 cref
          have h2_idx : (cref.setWidth 64 + (2 : BitVec 64)).toNat = cref.toNat + 2 := by
            rw [bv64_add2_toNat (by omega), hcr64]
          have h3_idx : (cref.setWidth 64 + (3 : BitVec 64)).toNat = cref.toNat + 3 := by
            rw [bv64_add3_toNat (by omega), hcr64]
          have h4_idx : (cref.setWidth 64 + (4 : BitVec 64)).toNat = cref.toNat + 4 := by
            rw [bv64_add4_toNat (by omega), hcr64]
          pp_head_steps
          · have hgt : st.arena_len % 2 ^ 64 < (cref.toNat + 3) % 2 ^ 64 := hc
            rw [Nat.mod_eq_of_lt (by omega : st.arena_len < 2 ^ 64),
              Nat.mod_eq_of_lt (by omega : cref.toNat + 3 < 2 ^ 64)] at hgt; omega
          · exact ih _ (off_v, p_v + (1 : BitVec 64) + (1 : BitVec 64), q_v, end_v, ()) m (by omega)
              ⟨_, rfl, propLit_inv_drop (ticks' := st.heur.search_ticks + (1 : BitVec 64))
                hpi hsw_drop hp2_nat, hoom_st, hm⟩
          · exact ih _ (off_v, p_v + (1 : BitVec 64) + (1 : BitVec 64), q_v, end_v, ()) m (by omega)
              ⟨_, rfl, propLit_inv_drop (ticks' := st.heur.search_ticks + (1 : BitVec 64))
                hpi hsw_drop hp2_nat, hoom_st, hm⟩
          · exact ih _ (off_v, p_v + (1 : BitVec 64) + (1 : BitVec 64), q_v, end_v, ()) m (by omega)
              ⟨_, rfl, propLit_inv_drop (ticks' := st.heur.search_ticks + (1 : BitVec 64))
                hpi hsw_drop hp2_nat, hoom_st, hm⟩
          · -- Live clause: `l0 = ar[cref+3]`, `l1 = ar[cref+4]`, then join `Js_3`
            let st_t : PlainState :=
              { st with heur := { st.heur with search_ticks := st.heur.search_ticks + 1#64 } }
            have hlen_t : st_t.LengthsOk c := hpi.len.with_heur (hpi.len.heur_ok.with_ticks _)
            have hng_t : arenaClauseGarb st_t cref.toNat = false := by
              unfold arenaClauseGarb arenaHdr
              have hget : st_t.arena[cref.toNat]? = some (st.arena[cref.toNat]'(by omega)) := by
                change st.arena[cref.toNat]? = _; exact List.getElem?_eq_getElem (by omega)
              rw [hget, Option.getD_some]
              have h0 : (st.arena[cref.toNat]'(by omega) &&& 0x00080000#32) = 0#32 := by assumption
              rw [h0]; rfl
            try clear hc; try clear hc; try clear hc; try clear hc
            have hnw_t : PlainCoreInv c F0 (withEmptyWatches c st_t) :=
              plainCoreInv_nw_congr hpi.nw hlen_t rfl rfl rfl rfl rfl rfl rfl rfl rfl
            have hsw_t : SplitWatchesInv c F0 st_t not_lit.toNat off_v.toNat q_v.toNat
                (p_v.toNat + 2) end_v.toNat := hsw_drop.with_nonwatch rfl rfl rfl rfl
            have hag_t : AgreesExcept (propLitMask s.heur) s st_t :=
              hpi.ag.update (fun t => { t with heur := st_t.heur })
            -- Join `Js_3`: `(other, ())` where `ar[cref+3] = other ∧ ar[cref+4] = not_lit`
            refine wp_join_group
              (fun (other, ()) mj => ∃ st1 : PlainState,
                PropLitInv c F0 s st1 not_lit.toNat off_v.toNat q_v.toNat (p_v.toNat + 2)
                  end_v.toNat ∧ st1.oom = 0#64 ∧ st1.arena_len = st.arena_len ∧
                cref.toNat ∈ arenaClauseRefs st1 ∧ arenaClauseGarb st1 cref.toNat = false ∧
                arenaClauseSize st1 cref.toNat = arenaClauseSize st cref.toNat ∧
                st1.arena[cref.toNat + 3]? = some other ∧
                st1.arena[cref.toNat + 4]? = some not_lit ∧ (PlainMem c st1 ⋆ R) mj) ?_ ?_
            · rintro _ ⟨other, ⟨⟩⟩ mj ⟨st1, hpi1, hoom1, halen1, hcr_ref1, hng1, hcsz1,
                har3, har4, hmj⟩
              have haren1 := hpi1.len.arena_len_arr; have halen1_le := hpi1.len.arena_len_le
              have hvals1 := hpi1.len.vals_len; have hwstk1 := hpi1.len.wstk_len_arr
              have hwvec1 := hpi1.len.wvec_len
              have hother_mem : other.toNat ∈ arenaClauseLits st1 cref.toNat := by
                refine (mem_arenaClauseLits_iff (by omega)).mpr ⟨0, by omega, ?_⟩
                exact congrArg BitVec.toNat (Option.some.inj
                  ((List.getElem?_eq_getElem (by omega)).symm.trans har3))
              have hother_lt : other.toNat < 2 * c.mv :=
                hpi1.nw.arena.lits_lt cref.toNat hcr_ref1 hng1 other.toNat hother_mem
              pp_head_steps
              · have hge : 2 * (c.mv % 2 ^ 64) % 2 ^ 64 ≤ other.toNat := hc
                rw [Nat.mod_eq_of_lt (by omega : c.mv < 2 ^ 64),
                  Nat.mod_eq_of_lt (by omega : 2 * c.mv < 2 ^ 64)] at hge
                omega
              · -- `vals[other] > 0`: keep large watch with blocking lit `other & 0x7FFFFFFF`
                exact ih _ (off_v, p_v + (1 : BitVec 64) + (1 : BitVec 64), q_v + (2 : BitVec 64),
                    end_v, ()) m (by omega)
                  ⟨_, rfl, propLit_inv_keep_large hpi1 hpi1.sw hnot_lt hq1_nat hq2_nat hp2_nat
                    (by omega) (by omega) (bv32_mask7f_flag0 other) hcr_lt hcr_ref1, hoom1, hm⟩
              · -- `vals[other] ≤ 0`: call `plain_find_repl(h, (u64)cref)`
                have hov_np : (0#32).slt ((st1.vals[other.toNat]'(by omega)).signExtend 32) =
                    false := hc
                try clear hc; try clear hc
                c0_call hFind
                refine ⟨c, st1, R, rfl, hpi1.len, by rw [hcr64]; omega, by rw [hcr64]; omega,
                  by rw [hcr64]; omega, hmj, ?_, ?_⟩
                · -- Case B2: `plain_find_repl` returned `0xFFFFFFFFULL` (no replacement)
                  intro hfind_bad
                  have hunit := propLit_hunit hpi1.nw hcr_ref1 hng1 (by omega) har3 har4
                    hpi1.not_f hfind_bad
                  pp_head_steps
                  · -- `ov < 0`: large clause conflict (`confl_type = 2`) & break
                    have hov_f := propLit_vals_neg hpi1.nw hother_lt (by omega) hc
                    have ⟨hpi_c, hcf_c⟩ := propLit_large_confl hpi1 hnot_lt hq_le hq1_nat hq2_nat
                      hp2_nat hcr_lt hcr_ref1 hng1 hov_f hunit
                    exact hB (off_v, p_v + (1 : BitVec 64) + (1 : BitVec 64),
                      q_v + (2 : BitVec 64), end_v, true, ()) m
                      ⟨_, hpi_c, by simp, fun _ => hcf_c, hm⟩
                  · -- `ov == 0`: keep large watch, call `plain_assign(h, other, cref)` & continue
                    have hov_un := propLit_vals_un hpi1.nw hother_lt (by omega) hov_np hc
                    have hsw2 := hpi1.sw.write_large hnot_lt hq_le (by omega) (by omega)
                      (bv32_mask7f_flag0 other) hcr_lt hcr_ref1
                    let st2 : PlainState :=
                      { st1 with
                        wstk := (st1.wstk.set q_v.toNat (other &&& 0x7FFFFFFF#32)).set
                          (q_v + (1 : BitVec 64)).toNat cref }
                    have hlen2 : st2.LengthsOk c :=
                      { hpi1.len with wstk_len_arr := by simp [st2, hwstk1] }
                    have hnw2 : PlainCoreInv c F0 (withEmptyWatches c st2) :=
                      plainCoreInv_nw_congr hpi1.nw hlen2 rfl rfl rfl rfl rfl rfl rfl rfl rfl
                    have hte_lt : st2.trail_end < c.mv :=
                      hnw2.trail_end_lt_of_unassigned hother_lt hov_un
                    have hcl_lt32 : st2.cur_level < 2 ^ 32 := by
                      have h1 : st2.cur_level ≤ st2.trail_end := hnw2.cur_level_le
                      have h2 : st2.trail_end ≤ c.mv := hlen2.trail_end_le; omega
                    have hng_guard : ¬ (c.mv ≤ other.toNat / 2 ∨ c.mv ≤ st2.trail_end) := by omega
                    c0_call hAssign
                    refine ⟨c, st2, R, rfl, hlen2, hcl_lt32, hm, ?_⟩
                    simp only [hng_guard, ↓reduceIte]
                    intro phases' m_as hph hlen_as hm_as
                    let st3 : PlainState :=
                      { st2 with
                        vals := (st2.vals.set other.toNat 1#8).set (other.toNat ^^^ 1) 0xFF#8
                        lvl := st2.lvl.set (other.toNat / 2) (BitVec.ofNat 32 st2.cur_level)
                        rsns := st2.rsns.set (other.toNat / 2)
                          (if st2.cur_level = 0 then 0xFFFFFFFF#32 else cref)
                        trl := st2.trl.set st2.trail_end other
                        trail_pos := st2.trail_pos.set (other.toNat / 2)
                          (BitVec.ofNat 32 st2.trail_end)
                        trail_end := st2.trail_end + 1
                        unflushed :=
                          if st2.cur_level = 0 then st2.unflushed + 1#64 else st2.unflushed
                        heur := { st2.heur with phases := phases' } }
                    have ⟨hnw3, hnot_f3, htr23⟩ := large_assign_nw_step hnw2 hcr_lt hcr_ref1 hng1
                      hother_lt hph hov_un hnot_lt hpi1.not_f hother_mem hunit
                      (unfl' := if st2.cur_level = 0 then st2.unflushed + 1#64 else st2.unflushed)
                    have hcl_eq : st2.cur_level = s.cur_level := hpi1.ag.get PlainState.cur_level
                    pp_head_steps
                    refine ih _ (off_v, p_v + (1 : BitVec 64) + (1 : BitVec 64),
                      q_v + (2 : BitVec 64), end_v, ()) m_as (by omega)
                      ⟨st3, rfl, ?_, hoom1, hm_as⟩
                    exact
                      { len := hlen_as, nw := hnw3
                        sw := by
                          rw [hp2_nat, hq2_nat]
                          exact hsw2.with_nonwatch rfl (by simp only [st3, st2, hq1_nat]) rfl rfl
                        ag := hpi1.ag.update (fun t => { t with
                          vals := st3.vals, lvl := st3.lvl, rsns := st3.rsns, trl := st3.trl,
                          trail_pos := st3.trail_pos, trail_end := st3.trail_end,
                          unflushed := st3.unflushed, wstk := st2.wstk, heur := st3.heur })
                        tr := (hpi1.tr.congr (s2 := st2) rfl rfl rfl).trans htr23 hcl_eq
                        rel := hpi1.rel, not_f := hnot_f3 }
                · -- Case B1: `plain_find_repl` found replacement at `2 ≤ r < sz`
                  intro r m_f hr2 hr_lt hcand hm_f
                  rw [hcr64] at hr_lt hcand hm_f
                  have hri_ne : BitVec.ofNat 64 r ≠ 0xFFFFFFFF#64 := fun h => by
                    have h1 : (BitVec.ofNat 64 r).toNat = r := bv64_ofNat_toNat (by omega)
                    have h2 : (0xFFFFFFFF#64).toNat = 0xFFFFFFFF := by decide
                    rw [h] at h1; omega
                  have hri_idx : (cref.setWidth 64 + (3 : BitVec 64) + BitVec.ofNat 64 r).toNat =
                      cref.toNat + 3 + r := by
                    rw [bv64_add_toNat (by rw [h3_idx, bv64_ofNat_toNat (by omega)]; omega),
                      h3_idx, bv64_ofNat_toNat (by omega)]
                  pp_head_steps
                  · let repl := (st1.arena.set (cref.toNat + 1) (BitVec.ofNat 32 r))[(
                        cref.setWidth 64 + (3 : BitVec 64) + BitVec.ofNat 64 r).toNat]'(
                        by simp; omega)
                    let st3 : PlainState :=
                      { st1 with arena := ((st1.arena.set (cref.toNat + 1) (BitVec.ofNat 32 r)).set
                        (cref.toNat + 4) repl).set (cref.toNat + 3 + r) not_lit }
                    have ⟨hlen3, hnw3, hsw3, hcr_ref3, hcsz3, hrepl_lt, hrepl_ne_not, hw0_ne_ff,
                        hcr_ne_ff, hm3⟩ := propLit_b1_swap (other := other) hpi1 (by omega)
                      hcr_ref1 (by omega) har4 hr2 hr_lt h4_idx hri_idx rfl hcand hm
                    c0_call hPush
                    refine ⟨c, st3, R, rfl, hlen3, hsw3.layout, fun h => absurd h (by decide),
                      fun _ => ⟨hw0_ne_ff, hcr_ne_ff⟩, hm3,
                      fun pok wvec' wstk' wlen' wu' wsort' m_p hlen_p hlay_p hpres_o hpok_t
                        hpok_f hm_p => ?_⟩
                    let st4 : PlainState :=
                      { st3 with
                        wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu',
                        heur := { st3.heur with wsort := wsort' } }
                    change (PlainMem c st4 ⋆ R) m_p at hm_p
                    have hnw4 : PlainCoreInv c F0 (withEmptyWatches c st4) :=
                      plainCoreInv_nw_congr hnw3 hlen_p rfl rfl rfl rfl rfl rfl rfl rfl rfl
                    have hwlen4_le : st4.wlen ≤ c.wcap := hlen_p.wlen_le
                    have hwvec'_len : st4.wvec.length = 4 * c.mv := hlen_p.wvec_len
                    have hwstk'_len : st4.wstk.length = c.wcap := hlen_p.wstk_len_arr
                    have hst3_alen : st3.arena.length = c.arena_cap := hlen3.arena_len_arr
                    have hst4_alen : st4.arena.length = c.arena_cap := hlen_p.arena_len_arr
                    have ⟨hoff4_bd, hoff4_nat, hp4_nat, hq4_nat, hend4_nat, hq4_1, hq4_2,
                        hsw4'⟩ := propLit_b1_after_push (st4 := st4) hidx0 hnot_lt hlen_p hlay_p
                      hsw3 rfl hrepl_lt hrepl_ne_not hcr_lt hcr_ref3 hp2_nat hq_le hpres_o
                      (fun ht => by
                        obtain ⟨_, _, hsz, hpre, hw0, hw1⟩ := hpok_t ht
                        exact ⟨hsz, hpre, hw0, hw1 rfl⟩)
                      (fun hf => (hpok_f hf).1 hrepl_lt)
                    let off4_v : BitVec 64 := (st4.wvec[((lit ^^^ (1 : BitVec 32)).setWidth 64 <<<
                      (1 : BitVec 64)).toNat]'(by omega)).setWidth 64
                    let q4_v := off4_v + (q_v - off_v)
                    have hoff4_bd' : watchOff st4 not_lit.toNat +
                        (end_v.toNat - off_v.toNat) ≤ st4.wlen := hoff4_bd
                    have hq4_nat_raw : ((st4.wvec[((lit ^^^ (1 : BitVec 32)).setWidth 64 <<<
                        (1 : Nat)).toNat]'(by rw [bv64_shl1_nat, bv32_xor_1]; omega)).setWidth 64 +
                        (q_v - off_v)).toNat =
                        watchOff st4 not_lit.toNat + (q_v.toNat - off_v.toNat) := hq4_nat
                    have hq4_1_raw : ((st4.wvec[((lit ^^^ (1 : BitVec 32)).setWidth 64 <<<
                        (1 : Nat)).toNat]'(by rw [bv64_shl1_nat, bv32_xor_1]; omega)).setWidth 64 +
                        (q_v - off_v) + (1 : BitVec 64)).toNat =
                        watchOff st4 not_lit.toNat + (q_v.toNat - off_v.toNat) + 1 := by
                      change (q4_v + (1 : BitVec 64)).toNat = _; rw [hq4_1, hq4_nat]
                    have hag4 : AgreesExcept (propLitMask s.heur) s st4 :=
                      hpi1.ag.update (fun t => { t with
                        arena := st4.arena, wvec := wvec', wstk := wstk', wlen := wlen',
                        wusable := wu', heur := st4.heur })
                    dsimp (config := { zeta := false }) only
                    pp_head_steps
                    · -- `pok = true`: continue loop at relocated `(off4, p4, q4, end4)`
                      have hp4_o :
                          (off4_v + (p_v + (1 : BitVec 64) + (1 : BitVec 64) - off_v)).toNat =
                            watchOff st4 not_lit.toNat + (p_v.toNat + 2 - off_v.toNat) := hp4_nat
                      have hend4_o : (off4_v + (end_v - off_v)).toNat =
                          watchOff st4 not_lit.toNat + (end_v.toNat - off_v.toNat) := hend4_nat
                      exact ih _ (off4_v,
                        off4_v + (p_v + (1 : BitVec 64) + (1 : BitVec 64) - off_v),
                        q4_v, off4_v + (end_v - off_v), ()) m_p
                        (by rw [hend4_o, hp4_o]
                            exact propLit_measure_lt (Nat.le_trans hpi1.sw.q_ge hq_le)
                              hpi1.sw.p_le_end)
                        ⟨st4, rfl, ⟨hlen_p, hnw4, hsw4', hag4, hpi1.tr.congr rfl rfl rfl, hpi1.rel,
                          hpi1.not_f⟩, hoom1, hm_p⟩
                    · -- `pok = false` (OOM): swap back, keep watch, set `oom = 1` & break
                      have ⟨hpi6, hm6⟩ := propLit_b1_oom hpi1 hlen_p hnw4 hsw4' rfl rfl hpi1.rel
                        hag4 (hpi1.tr.congr rfl rfl rfl) hpi1.not_f hnot_lt hq_le hcr_lt hcr_ref3
                        hflag (by change _ + arenaClauseSize st3 _ ≤ _; rw [hcsz3]; omega)
                        hr2 (by change r < arenaClauseSize st3 _; rw [hcsz3]; omega)
                        h4_idx hri_idx hq4_nat hp4_nat hend4_nat hq4_1 hq4_2 hm
                      exact hB (off4_v, off4_v + (p_v + (1 : BitVec 64) + (1 : BitVec 64) - off_v),
                        q4_v + (2 : BitVec 64), off4_v + (end_v - off_v), true, ()) m
                        ⟨_, hpi6, by simp, fun _ => Or.inl (by show (1 : BitVec 64) ≠ 0#64; decide),
                          hm6⟩
                  · exact absurd (by assumption) hri_ne
                  · exact absurd (by assumption) hri_ne
            · intro J3 hJ3; pp_head_steps
              · let l1 := st.arena[(cref.setWidth 64 + (4 : BitVec 64)).toNat]'(by omega)
                have ⟨hpi1, href1, hng1, hcsz1, har3, har4, hm1⟩ := propLit_js3_swap hlen_t hnw_t
                  hsw_t hag_t (hpi.tr.congr rfl rfl rfl) hpi.rel hpi.not_f hcr_ref hng_t hcsz3
                  hcr_fit h3_idx h4_idx
                  (by change st.arena[cref.toNat + 3]'_ = not_lit
                      rw [← (by assumption :
                        st.arena[(cref.setWidth 64 + (3 : BitVec 64)).toNat]'(by omega) = not_lit)]
                      congr 1; exact h3_idx.symm)
                  (by change st.arena[cref.toNat + 4]'_ = l1; dsimp only [l1]; congr 1
                      exact h4_idx.symm) hm
                exact hJ3 (l1, ()) m ⟨_, hpi1, hoom_st, rfl, href1, hng1, hcsz1, har3, har4, hm1⟩
              · exact ih _ (off_v, p_v + (1 : BitVec 64) + (1 : BitVec 64), q_v, end_v, ()) m
                  (by omega) ⟨st_t, rfl, ⟨hlen_t, hnw_t, by rw [hp2_nat]; exact hsw_t, hag_t,
                    hpi.tr.congr rfl rfl rfl, hpi.rel, hpi.not_f⟩, hoom_st, hm⟩
              · let l0 := st.arena[(cref.setWidth 64 + (3 : BitVec 64)).toNat]'(by omega)
                have hl1_not : st.arena[(cref.setWidth 64 + (4 : BitVec 64)).toNat]'(by omega) =
                    not_lit := hc
                exact hJ3 (l0, ()) m ⟨st_t, ⟨hlen_t, hnw_t, hsw_t, hag_t,
                    hpi.tr.congr rfl rfl rfl, hpi.rel, hpi.not_f⟩,
                  hoom_st, rfl, hcr_ref, hng_t, rfl,
                  by change st.arena[cref.toNat + 3]? = some l0
                     rw [← h3_idx]; exact List.getElem?_eq_getElem (by omega),
                  by change st.arena[cref.toNat + 4]? = some not_lit
                     rw [← hl1_not, ← h4_idx]; exact List.getElem?_eq_getElem (by omega), hm⟩
        · intro J2 hJ2; pp_head_steps
          · exact ih _ (off_v, p_v + (1 : BitVec 64) + (1 : BitVec 64), q_v + (2 : BitVec 64),
                end_v, ()) m (by omega)
              ⟨_, rfl, propLit_inv_keep_large hpi hsw_drop hnot_lt hq1_nat hq2_nat hp2_nat
                (by omega) (by omega) hflag hcr_lt hcr_ref, hoom_st, hm⟩
          · exact hJ2 () ml rfl
          · exact hJ2 () ml rfl
      · exact hB (off_v, p_v, q_v, end_v, false, ()) ml ⟨st, hpi, fun _ => hoom_st, by simp, hml⟩
    · intro _ L _ hL; pp_head_steps
      have hoff_bd := hinv.watches.bounds not_lit.toNat hnot_lt; have hwlen_le := hlen0.wlen_le
      have hoff_nat : ((s.wvec[((lit ^^^ (1 : BitVec 32)).setWidth 64 <<<
          (1 : BitVec 64)).toNat]'(by omega)).setWidth 64).toNat = watchOff s not_lit.toNat := by
        rw [bv_c0_zext32_64, hoff0_eq]
      have hsz_nat : ((s.wvec[(((lit ^^^ (1 : BitVec 32)).setWidth 64 <<< (1 : BitVec 64)) +
          (1 : BitVec 64)).toNat]'(by omega)).setWidth 64).toNat = watchSize s not_lit.toNat := by
        rw [bv_c0_zext32_64, hsz0_eq]
      have hend_nat : ((s.wvec[((lit ^^^ (1 : BitVec 32)).setWidth 64 <<<
            (1 : BitVec 64)).toNat]'(by omega)).setWidth 64 +
          (s.wvec[(((lit ^^^ (1 : BitVec 32)).setWidth 64 <<< (1 : BitVec 64)) +
            (1 : BitVec 64)).toNat]'(by omega)).setWidth 64).toNat =
          watchOff s not_lit.toNat + watchSize s not_lit.toNat := by
        rw [bv64_add_toNat (by omega), hoff_nat, hsz_nat]
      have hoff_g : ∀ h, ((s.wvec[((lit ^^^ (1 : BitVec 32)).setWidth 64 <<<
          (1 : Nat)).toNat]'h).setWidth 64).toNat = watchOff s not_lit.toNat := fun _ => hoff_nat
      have hend_g : ∀ h1 h2, ((s.wvec[((lit ^^^ (1 : BitVec 32)).setWidth 64 <<<
            (1 : Nat)).toNat]'h1).setWidth 64 +
          (s.wvec[(((lit ^^^ (1 : BitVec 32)).setWidth 64 <<< (1 : Nat)) +
            (1 : BitVec 64)).toNat]'h2).setWidth 64).toNat =
          watchOff s not_lit.toNat + watchSize s not_lit.toNat := fun _ _ => hend_nat
      refine hL _ _ m ⟨st0, rfl, ?_, hoom0, hm⟩; rw [hend_g, hoff_g]; exact hpi0

end LeanQbe.T.Examples.Kissat.Plain
