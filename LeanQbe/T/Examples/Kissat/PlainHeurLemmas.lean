module

public import LeanQbe.T.Examples.Kissat.PlainHeurLemmas1
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Plain` Heuristic `Func.wp` Proofs — Part 2 (`Wave 2b`)

Proves parametric `(Γ : Env)` `Func.wp` contracts for 11 helpers in `Plain1`
matching `plainSpecTable` rows (`PlainSpec.lean:837-847`):
6. `plain_watch_push`, 7. `plain_heap_up`, 8. `plain_heap_down`, 9. `plain_heap_push`,
10. `plain_heap_pop`, 11. `plain_rescale`, 12. `plain_bump_var`, 13. `plain_bump_decay`,
14. `plain_queue_mtf`, 15. `plain_tick_rel`, 16. `plain_ema_update`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Plain

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.C0Step
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test
open scoped PlainHeurTactics

/-! ## 1. Binary max-heap (`heap_up`, `heap_down`, `heap_push`, `heap_pop`) -/

theorem plain_heap_up_wp (Γ : Env) :
    ∀ a m Q X, plainHeapUpSpec a m Q X → Func.wp Γ plain_heap_up_body a m Q X := by
  rintro ⟨h, v, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  obtain hmv : c.mv < 2 ^ 28 := c.hmv
  obtain hok := hlen.heur_ok
  obtain hhl := hok.heap_len_arr; obtain hpl := hok.pos_len; obtain hsl := hok.score_len
  c0_steps
  · exact hQ s.heur m hok rfl hm
  · exact hQ s.heur m hok rfl hm
  · exact hQ s.heur m hok rfl hm
  · exact hQ s.heur m hok rfl hm
  · obtain hv : v.toNat < c.mv := by c0_bound
    obtain hp_lt : (s.heur.pos[v.toNat % 2 ^ 64]'(by omega)).toNat < c.mv := by c0_bound
    refine wp_loop_inv
      (fun (p, ()) m1 => p.toNat < c.mv ∧ ∃ heur1 : PlainHeur,
        heur1.LengthsOk c ∧ heur1.rel_trigger = s.heur.rel_trigger ∧
        (PlainMem c { s with heur := heur1 } ⋆ R) m1)
      (fun (p, ()) _ => p.toNat) (fun J hLoop => ?_)
      (fun J (p, ()) m1 ⟨hp, heur1, hok1, hrt1, hm1⟩ hLoop => ?_)
    · c0_steps
      exact hLoop _ _ ⟨by simpa [BitVec.toNat_setWidth] using hp_lt, s.heur, hok, rfl, hm⟩
    · obtain hhl1 := hok1.heap_len_arr; obtain hpl1 := hok1.pos_len; obtain hsl1 := hok1.score_len
      c0_steps
      · refine hQ _ _ ?_ ?_ hm
        exact { hok1 with heap_len_arr := by simp [hhl1], pos_len := by simp [hpl1] }; exact hrt1
      · refine hQ _ _ ?_ ?_ hm
        exact { hok1 with heap_len_arr := by simp [hhl1], pos_len := by simp [hpl1] }; exact hrt1
      · obtain hp0 : 0 < p.toNat := by c0_bound
        obtain hpp_lt : ((p - 1) >>> (1 : Nat)).toNat < p.toNat := by
          have hsub : (p - 1).toNat = p.toNat - 1 := by bv_omega
          rw [BitVec.toNat_ushiftRight, hsub]; simp [Nat.shiftRight_eq_div_pow]; omega
        obtain hpp_mv : ((p - 1) >>> (1 : Nat)).toNat < c.mv := by omega
        obtain hpv_lt :
            (BitVec.setWidth 64
              (heur1.heap[(BitVec.setWidth 64 ((p - 1) >>> (1 : Nat))).toNat]'(by
                rw [hhl1, BitVec.toNat_setWidth]; omega))).toNat < heur1.pos.length := by
          simp only [hpl1, BitVec.toNat_setWidth]; omega
        c0_steps; refine hLoop _ _ hpp_lt ⟨hpp_mv, _, ?_, ?_, hm⟩
        exact { hok1 with heap_len_arr := by simp [hhl1], pos_len := by simp [hpl1] }; exact hrt1
      · refine hQ _ _ ?_ ?_ hm
        exact { hok1 with heap_len_arr := by simp [hhl1], pos_len := by simp [hpl1] }; exact hrt1

theorem plain_heap_down_wp (Γ : Env) :
    ∀ a m Q X, plainHeapDownSpec a m Q X → Func.wp Γ plain_heap_down_body a m Q X := by
  rintro ⟨h, v, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  obtain hmv : c.mv < 2 ^ 28 := c.hmv; obtain hok := hlen.heur_ok
  obtain hhl := hok.heap_len_arr; obtain hpl := hok.pos_len; obtain hsl := hok.score_len
  c0_steps
  · exact hQ s.heur m hok rfl rfl hm
  · exact hQ s.heur m hok rfl rfl hm
  · exact hQ s.heur m hok rfl rfl hm
  · exact hQ s.heur m hok rfl rfl hm
  · obtain hv : v.toNat < c.mv := by c0_bound
    obtain hhle : (BitVec.ofNat 64 s.heur.heap_len).toNat ≤ c.mv := by c0_bound
    obtain hp0_lt : (s.heur.pos[v.toNat % 2 ^ 64]'(by omega)).toNat <
        (BitVec.ofNat 64 s.heur.heap_len).toNat := by c0_bound
    refine wp_loop_inv
      (fun (p, ()) m1 => p.toNat < (BitVec.ofNat 64 s.heur.heap_len).toNat ∧
        ∃ heur1 : PlainHeur, heur1.LengthsOk c ∧ heur1.heap_len = s.heur.heap_len ∧
          heur1.rel_trigger = s.heur.rel_trigger ∧ (PlainMem c { s with heur := heur1 } ⋆ R) m1)
      (fun (p, ()) _ => (BitVec.ofNat 64 s.heur.heap_len).toNat - p.toNat) (fun J hLoop => ?_)
      (fun J (p, ()) m1 ⟨hp, heur1, hok1, hhl_eq, hrt_eq, hm1⟩ hLoop => ?_)
    · c0_steps
      exact hLoop _ _ ⟨by simpa [BitVec.toNat_setWidth] using hp0_lt, s.heur, hok, rfl, rfl, hm⟩
    · obtain hhl1 := hok1.heap_len_arr; obtain hpl1 := hok1.pos_len; obtain hsl1 := hok1.score_len
      obtain hp_mv : p.toNat < c.mv := by omega
      obtain hsh_p : (p.setWidth 64 <<< (1 : Nat)).toNat = 2 * p.toNat := by
        rw [BitVec.toNat_shiftLeft, zext_toNat p (by decide)]; simp [Nat.shiftLeft_eq]; omega
      obtain hcp_toNat : ((p.setWidth 64 <<< (1 : Nat)) + 1).toNat = 2 * p.toNat + 1 := by
        rw [BitVec.toNat_add, hsh_p]; simp; omega
      c0_to_group
      · refine hQ _ _ ?_ ?_ ?_ hm
        { exact { hok1 with heap_len_arr := by simp [hhl1], pos_len := by simp [hpl1] } }
        { exact hhl_eq }; exact hrt_eq
      · refine hQ _ _ ?_ ?_ ?_ hm
        { exact { hok1 with heap_len_arr := by simp [hhl1], pos_len := by simp [hpl1] } }
        { exact hhl_eq }; exact hrt_eq
      · refine wp_join_group
          (fun (cp', cv', _csc', ()) m2 => p.toNat < cp'.toNat ∧
            cp'.toNat < (BitVec.ofNat 64 s.heur.heap_len).toNat ∧ cv'.toNat < c.mv ∧ m1 = m2)
          (fun _ (cp', cv', csc', ()) m2 ⟨hgt, hlt, hcv_mv, hm2⟩ => ?_) ?_
        · rcases hm2 with rfl; c0_steps
          · refine hQ _ _ ?_ ?_ ?_ hm
            { exact { hok1 with heap_len_arr := by simp [hhl1], pos_len := by simp [hpl1] } }
            { exact hhl_eq }; exact hrt_eq
          · obtain htr : (cp'.setWidth 32).toNat = cp'.toNat := by
              rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
            refine hLoop _ _ (by dsimp only; omega) ⟨by omega, _, ?_, ?_, ?_, hm⟩
            { exact { hok1 with heap_len_arr := by simp [hhl1], pos_len := by simp [hpl1] } }
            { exact hhl_eq }; exact hrt_eq
        · intro Jm hJm; c0_steps
          · obtain h1v : (1 : Val i64).toNat = 1 := rfl
            obtain hsp_eq : (BitVec.setWidth 64 p <<< (1 : Nat) + 1 + 1).toNat =
                ((BitVec.setWidth 64 p <<< (1 : Nat)).toNat + (1 : Val i64).toNat +
                  (1 : Val i64).toNat) % 2 ^ 64 := by
              rw [BitVec.toNat_add, hcp_toNat, hsh_p, h1v]
            obtain hsv_lt :
                (BitVec.setWidth 64
                  (heur1.heap[(BitVec.setWidth 64 p <<< (1 : Nat) + 1 + 1).toNat]'(by
                    rw [hhl1, hsp_eq]
                    simp only [hsh_p, h1v, BitVec.toNat_ofNat] at *; omega))).toNat <
                heur1.score.length := by
              simp only [hsl1, BitVec.toNat_setWidth, hsp_eq]; omega
            c0_steps
            exact hJm _ _ ⟨by rw [BitVec.toNat_add, hcp_toNat]; simp; omega,
              by rw [hsp_eq]; simp only [BitVec.toNat_ofNat, hsh_p, h1v] at *; omega,
              by simp only [BitVec.toNat_setWidth, hsl1] at hsv_lt; omega, rfl⟩
          all_goals
            have h1v : (1 : Val i64).toNat = 1 := rfl
            refine hJm _ _ ⟨by rw [hcp_toNat]; omega,
              by rw [hcp_toNat]; simp only [BitVec.toNat_ofNat, hsh_p, h1v] at *; omega, ?_, rfl⟩
            have hcp_eq : (BitVec.setWidth 64 p <<< (1 : Nat) + 1).toNat =
                ((BitVec.setWidth 64 p <<< (1 : Nat)).toNat + (1 : Val i64).toNat) % 2 ^ 64 := by
              rw [hcp_toNat, hsh_p, h1v]; omega
            simp only [hcp_eq]; simp only [BitVec.toNat_ofNat] at *; omega
      · cases hc

theorem plain_heap_push_wp (Γ : Env)
    (hUp : ∀ a m Q X, plainHeapUpSpec a m Q X → Γ "plain_heap_up" [i64, i32] [] a m Q X) :
    ∀ a m Q X, plainHeapPushSpec a m Q X → Func.wp Γ plain_heap_push_body a m Q X := by
  rintro ⟨h, v, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  obtain hmv : c.mv < 2 ^ 28 := c.hmv; obtain hok := hlen.heur_ok
  obtain hhl := hok.heap_len_arr; obtain hpl := hok.pos_len
  c0_steps
  · exact hQ s.heur m hok rfl hm
  · exact hQ s.heur m hok rfl hm
  · exact hQ s.heur m hok rfl hm
  · c0_call hUp
    refine ⟨c, _, R, rfl, ?_, hm, ?_⟩
    · exact hlen.with_heur { hok with heap_len_arr := by simp [hhl], pos_len := by simp [hpl] }
    · intro heur' m' hok' hrt' hm'; c0_steps; exact hQ heur' m' hok' hrt' hm'

theorem plain_heap_pop_wp (Γ : Env)
    (hDown : ∀ a m Q X, plainHeapDownSpec a m Q X → Γ "plain_heap_down" [i64, i32] [] a m Q X) :
    ∀ a m Q X, plainHeapPopSpec a m Q X → Func.wp Γ plain_heap_pop_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  obtain hmv : c.mv < 2 ^ 28 := c.hmv; obtain hok := hlen.heur_ok
  obtain hhl := hok.heap_len_arr; obtain hpl := hok.pos_len
  obtain hnlen_sub : 0 < s.heur.heap_len ∧ s.heur.heap_len ≤ c.mv →
      (BitVec.ofNat 64 s.heur.heap_len - 1).toNat = s.heur.heap_len - 1 := fun ⟨hpos, hle⟩ => by
    have h1 := bv64_ofNat_toNat (n := s.heur.heap_len) (by omega)
    have : 0 < (BitVec.ofNat 64 s.heur.heap_len).toNat := by omega
    bv_omega
  c0_steps
  · exact hQ 0xFFFFFFFF#64 s.heur m (Or.inl rfl) hok (fun ⟨hpos, hle⟩ => by
      have := bv64_ofNat_toNat (n := s.heur.heap_len) (by omega)
      rw [hc] at this; simp at this; omega) rfl hm
  · exact hQ 0xFFFFFFFF#64 s.heur m (Or.inl rfl) hok (fun ⟨_, hle⟩ => by
      have h1 : c.mv < (BitVec.ofNat 64 s.heur.heap_len).toNat := by c0_bound
      rw [bv64_ofNat_toNat (by omega)] at h1; omega) rfl hm
  all_goals
    first
    | (c0_call hDown; refine ⟨c, _, R, rfl, ?_, hm, ?_⟩;
       { exact hlen.with_heur { hok with
           heap_len_arr := by simp [hhl], pos_len := by simp [hpl] } };
       { intro heur' m' hok' hhl' hrt' hm'; c0_steps;
         all_goals first
         | exact hQ 0xFFFFFFFF#64 heur' m' (Or.inl rfl) hok'
             (fun h => by rw [hhl']; exact hnlen_sub h) hrt' hm'
         | exact hQ _ heur' m' (Or.inr (by c0_bound)) hok'
             (fun h => by rw [hhl']; exact hnlen_sub h) hrt' hm' })
    | (refine hQ 0xFFFFFFFF#64 _ _ (Or.inl rfl) ?_ ?_ ?_ hm;
       { exact { hok with heap_len_arr := by simp [hhl], pos_len := by simp [hpl] } };
       { exact hnlen_sub }; { rfl })
    | (refine hQ _ _ _ (Or.inr (by c0_bound)) ?_ ?_ ?_ hm;
       { exact { hok with heap_len_arr := by simp [hhl], pos_len := by simp [hpl] } };
       { exact hnlen_sub }; { rfl })

/-! ## 2. VSIDS rescaling & bumping (`plain_rescale`, `plain_bump_var`, `plain_bump_decay`) -/

theorem plain_rescale_wp (Γ : Env) :
    ∀ a m Q X, plainRescaleSpec a m Q X → Func.wp Γ plain_rescale_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  obtain hmv : c.mv < 2 ^ 28 := c.hmv; obtain hok := hlen.heur_ok
  c0_steps
  refine wp_loop_inv
    (fun (v, ()) m1 => v.toNat ≤ c.mv ∧ ∃ heur1 : PlainHeur,
      heur1.LengthsOk c ∧ (PlainMem c { s with heur := heur1 } ⋆ R) m1)
    (fun (v, ()) _ => c.mv - v.toNat) (fun J hLoop => ?_)
    (fun J (v, ()) m1 ⟨hvle, heur1, hok1, hm1⟩ hLoop => ?_)
  · c0_steps; exact hLoop _ _ ⟨by simp, s.heur, hok, hm⟩
  · obtain hsl1 := hok1.score_len; c0_steps
    · refine hLoop _ _ (by c0_bound) ⟨by c0_bound, _, ?_, hm⟩
      exact { hok1 with score_len := by simp [hsl1] }
    · refine hQ _ _ ?_ hm; exact { hok1 with heap_len_arr := hok1.heap_len_arr }
    · refine hQ _ _ ?_ hm; exact { hok1 with heap_len_arr := hok1.heap_len_arr }

theorem plain_bump_var_wp (Γ : Env)
    (hUp : ∀ a m Q X, plainHeapUpSpec a m Q X → Γ "plain_heap_up" [i64, i32] [] a m Q X)
    (hRes : ∀ a m Q X, plainRescaleSpec a m Q X → Γ "plain_rescale" [i64] [] a m Q X) :
    ∀ a m Q X, plainBumpVarSpec a m Q X → Func.wp Γ plain_bump_var_body a m Q X := by
  rintro ⟨h, v, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  obtain hmv : c.mv < 2 ^ 28 := c.hmv; obtain hok := hlen.heur_ok; obtain hsl := hok.score_len
  c0_steps
  · exact hQ s.heur m hok hm
  all_goals
    c0_call hUp; refine ⟨c, _, R, rfl, ?_, hm, ?_⟩
    · exact hlen.with_heur { hok with score_len := by simp [hsl] }
    · intro heur1 m1 hok1 _hrt1 hm1; c0_steps
      all_goals first
      | (c0_call hRes; refine ⟨c, _, R, rfl, hlen.with_heur hok1, hm1, ?_⟩;
         intro heur2 m2 hok2 hm2; c0_steps; exact hQ heur2 m2 hok2 hm2)
      | exact hQ heur1 m1 hok1 hm1

theorem plain_bump_decay_wp (Γ : Env)
    (hRes : ∀ a m Q X, plainRescaleSpec a m Q X → Γ "plain_rescale" [i64] [] a m Q X) :
    ∀ a m Q X, plainBumpDecaySpec a m Q X → Func.wp Γ plain_bump_decay_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  obtain hok := hlen.heur_ok; c0_steps
  all_goals first
  | (c0_call hRes; refine ⟨c, _, R, rfl, ?_, hm, ?_⟩;
     { exact hlen.with_heur { hok with heap_len_arr := hok.heap_len_arr } };
     { intro heur1 m1 hok1 hm1; c0_steps;
       all_goals first
       | exact hQ heur1 m1 hok1 hm1
       | (c0_call hRes; refine ⟨c, _, R, rfl, ?_, hm, ?_⟩;
          { exact hlen.with_heur { hok1 with heap_len_arr := hok1.heap_len_arr } };
          { intro heur2 m2 hok2 hm2; c0_steps; exact hQ heur2 m2 hok2 hm2 })
       | (refine hQ _ _ ?_ hm; exact { hok1 with heap_len_arr := hok1.heap_len_arr }) })
  | (refine hQ _ _ ?_ hm; exact { hok with heap_len_arr := hok.heap_len_arr })

/-! ## 3. VMTF queue, reluctant doubling, and Q24 EMA -/

theorem plain_queue_mtf_wp (Γ : Env) :
    ∀ a m Q X, plainQueueMtfSpec a m Q X → Func.wp Γ plain_queue_mtf_body a m Q X := by
  rintro ⟨h, v, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  obtain hmv : c.mv < 2 ^ 28 := c.hmv; obtain hok := hlen.heur_ok; obtain hvl := hlen.vals_len
  obtain hqpl := hok.q_prev_len; obtain hqnl := hok.q_next_len; obtain hqsl := hok.q_stamp_len
  c0_to_group
  · exact hQ s.heur m hok hm
  · exact hQ s.heur m hok hm
  · rename_i hlt_mv
    obtain hv : v.toNat < c.mv := by c0_bound
    obtain hv2 : (v.setWidth 64 <<< (1 : Nat)).toNat < s.vals.length := by
      rw [BitVec.toNat_shiftLeft, zext_toNat v (by decide)]; simp [Nat.shiftLeft_eq, hvl]; omega
    clear hlt_mv hc; c0_to_group
    refine wp_join_group (fun _ m1 => ∃ heur1 : PlainHeur, heur1.LengthsOk c ∧
      (PlainMem c { s with heur := heur1 } ⋆ R) m1) ?_ ?_
    · rintro _ _ m1 ⟨heur1, hok1, hm1⟩; clear hm hok hqpl hqnl hqsl
      obtain hqpl1 := hok1.q_prev_len; obtain hqnl1 := hok1.q_next_len; c0_to_group
      refine wp_join_group (fun _ m2 => ∃ heur2 : PlainHeur, heur2.LengthsOk c ∧
        (PlainMem c { s with heur := heur2 } ⋆ R) m2) ?_ ?_
      · rintro _ _ m2 ⟨heur2, hok2, hm2⟩; clear hm hok1
        obtain hqpl2 := hok2.q_prev_len; obtain hqnl2 := hok2.q_next_len; c0_to_group
        refine wp_join_group (fun _ m3 => ∃ heur3 : PlainHeur, heur3.LengthsOk c ∧
          (PlainMem c { s with heur := heur3 } ⋆ R) m3) ?_ ?_
        · rintro _ _ m3 ⟨heur3, hok3, hm3⟩; clear hm2 hok2 hqpl2 hqnl2 hqpl1 hqnl1
          obtain hqpl3 := hok3.q_prev_len; obtain hqnl3 := hok3.q_next_len; c0_to_group
          refine wp_join_group (fun _ m4 => ∃ heur4 : PlainHeur, heur4.LengthsOk c ∧
            (PlainMem c { s with heur := heur4 } ⋆ R) m4) ?_ ?_
          · rintro _ _ m4 ⟨heur4, hok4, hm4⟩; clear hm hok3 hqpl3 hqnl3
            obtain hqnl4 := hok4.q_next_len; obtain hqsl4 := hok4.q_stamp_len; c0_to_group
            refine wp_join_group (fun _ m5 => ∃ heur5 : PlainHeur, heur5.LengthsOk c ∧
              (PlainMem c { s with heur := heur5 } ⋆ R) m5) ?_ ?_
            · rintro _ _ m5 ⟨heur5, hok5, hm5⟩; clear hm4 hok4 hqnl4 hqsl4
              obtain hqsl5 := hok5.q_stamp_len; c0_steps
              · refine hQ _ _ ?_ hm; exact { hok5 with heap_len_arr := hok5.heap_len_arr }
              · exact hQ heur5 m5 hok5 hm5
            · intro J5 hJ5; c0_to_group
              · clear hc
                refine wp_loop_inv (fun (_st, _cur, steps, ()) mL => steps.toNat ≤ c.mv ∧
                    ∃ heurL : PlainHeur, heurL.LengthsOk c ∧
                      (PlainMem c { s with heur := heurL } ⋆ R) mL)
                  (fun (_, _, steps, ()) _ => c.mv - steps.toNat) (fun J hLoop => ?_) ?_
                · c0_steps; exact hLoop _ _ ⟨by simp, heur4, hok4, hm4⟩
                · rintro J ⟨st, cur, steps, ⟨⟩⟩ mL ⟨hsle, heurL, hokL, hmL⟩ hLoop
                  clear hm4 hok4 hqnl4 hqsl4
                  obtain hqnlL := hokL.q_next_len; obtain hqslL := hokL.q_stamp_len
                  refine wp_join_group (fun _ mE => ∃ heurE : PlainHeur, heurE.LengthsOk c ∧
                    (PlainMem c { s with heur := heurE } ⋆ R) mE) ?_ ?_
                  · rintro _ _ mE ⟨heurE, hokE, hmE⟩
                    clear hmL hokL hqnlL hqslL hsle hLoop hv2 hvl hv
                    obtain hqslE := hokE.q_stamp_len; c0_steps
                    all_goals
                      refine hJ5 _ _ ⟨_, ?_, hm⟩
                      exact { hokE with heap_len_arr := hokE.heap_len_arr }
                  · intro JE hJE; c0_steps
                    · refine hLoop _ _ (by c0_bound) ⟨by c0_bound, _, ?_, hm⟩
                      exact { hokL with q_stamp_len := by simp [hqslL] }
                    · exact hJE _ _ ⟨heurL, hokL, hmL⟩
                    · exact hJE _ _ ⟨heurL, hokL, hmL⟩
              · c0_steps
                refine hJ5 _ _ ⟨_, ?_, hm⟩; exact { hok4 with q_stamp_len := by simp [hqsl4] }
          · intro J4 hJ4; c0_steps; all_goals
              refine hJ4 _ _ ⟨_, ?_, hm⟩
              exact { hok3 with q_prev_len := by simp [hqpl3], q_next_len := by simp [hqnl3] }
        · intro J3 hJ3; c0_steps; all_goals
            refine hJ3 _ _ ⟨_, ?_, hm⟩
            exact { hok2 with q_prev_len := by simp [hqpl2], q_next_len := by simp [hqnl2] }
      · intro J2 hJ2; c0_steps; all_goals
          refine hJ2 _ _ ⟨_, ?_, hm⟩
          exact { hok1 with q_prev_len := by simp [hqpl1], q_next_len := by simp [hqnl1] }
    · intro J1 hJ1; c0_steps
      all_goals refine hJ1 _ _ ⟨_, ?_, hm⟩; exact { hok with heap_len_arr := hok.heap_len_arr }

theorem plain_tick_rel_wp (Γ : Env) :
    ∀ a m Q X, plainTickRelSpec a m Q X → Func.wp Γ plain_tick_rel_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  obtain hok := hlen.heur_ok; c0_to_group
  · exact hQ s.heur m hok hm
  · exact hQ s.heur m hok hm
  · refine wp_join_group (fun _ m1 => ∃ heur1 : PlainHeur, heur1.LengthsOk c ∧
      (PlainMem c { s with heur := heur1 } ⋆ R) m1) (fun _ _ m1 ⟨heur1, hok1, hm1⟩ => ?_) ?_
    · clear hm; c0_to_group
      · exact hQ heur1 m1 hok1 hm1
      · refine wp_join_group (fun _ m2 => m1 = m2) (fun _ _ m2 hm2 => ?_) ?_
        · rcases hm2 with rfl; c0_to_group
          refine wp_join_group (fun _ m3 => m1 = m3) (fun _ _ m3 hm3 => ?_) ?_
          · rcases hm3 with rfl; c0_to_group
            refine wp_join_group (fun _ m4 => m1 = m4) (fun _ _ m4 hm4 => ?_) ?_
            · rcases hm4 with rfl; c0_steps
              all_goals refine hQ _ _ ?_ hm; exact { hok1 with heap_len_arr := hok1.heap_len_arr }
            · intro Jm hJm; c0_steps; all_goals exact hJm _ _ rfl
          · intro Jm hJm; c0_steps; all_goals exact hJm _ _ rfl
        · intro Jm hJm; c0_steps; all_goals exact hJm _ _ rfl
    · intro Jm hJm; c0_steps
      · refine hJm _ _ ⟨_, ?_, hm⟩; exact { hok with heap_len_arr := hok.heap_len_arr }
      · exact hJm _ _ ⟨s.heur, hok, hm⟩

theorem plain_ema_update_wp (Γ : Env) :
    ∀ a m Q X, plainEmaUpdateSpec a m Q X → Func.wp Γ plain_ema_update_body a m Q X := by
  rintro ⟨h, glue, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  obtain hok := hlen.heur_ok; c0_to_group
  refine wp_join_group (fun _ m1 => m = m1) (fun _ _ m1 hm1 => ?_) ?_
  · rcases hm1 with rfl; c0_to_group
    refine wp_join_group (fun _ m2 => m = m2) (fun _ _ m2 hm2 => ?_) ?_
    · rcases hm2 with rfl; c0_to_group
      refine wp_join_group (fun _ m3 => ∃ heur1 : PlainHeur, heur1.LengthsOk c ∧
          heur1.rel_trigger = s.heur.rel_trigger ∧ (PlainMem c { s with heur := heur1 } ⋆ R) m3)
        (fun _ _ m3 ⟨heur1, hok1, hrt1, hm3⟩ => ?_) ?_
      · clear hm; c0_to_group
        refine wp_join_group (fun _ m4 => m3 = m4) (fun _ _ m4 hm4 => ?_) ?_
        · rcases hm4 with rfl; c0_steps
          all_goals
            refine hQ _ _ ?_ ?_ hm
            { exact { hok1 with heap_len_arr := hok1.heap_len_arr } }; exact hrt1
        · intro Jm hJm; c0_steps; all_goals exact hJm _ _ rfl
      · intro Jm hJm; c0_steps
        all_goals
          refine hJm _ _ ⟨_, ?_, ?_, hm⟩
          { exact { hok with heap_len_arr := hok.heap_len_arr } }; rfl
    · intro Jm hJm; c0_steps; all_goals exact hJm _ _ rfl
  · intro Jm hJm; c0_steps; all_goals exact hJm _ _ rfl

/-! ## 4. Watch stack push (`plain_watch_push`) -/

private abbrev wOff (wvec : List (BitVec 32)) (l : Nat) : Nat := (wvec[2 * l]?.getD 0#32).toNat
private abbrev wSz (wvec : List (BitVec 32)) (l : Nat) : Nat := (wvec[2 * l + 1]?.getD 0#32).toNat

private def WatchPresAll (c : PlainCfg) (s s1 : PlainState) : Prop :=
  ∀ l < 2 * c.mv, watchSize s1 l = watchSize s l ∧
    ∀ k < watchSize s l, s1.wstk[watchOff s1 l + k]? = s.wstk[watchOff s l + k]?

private theorem watchPresAll_refl (c : PlainCfg) (s : PlainState) : WatchPresAll c s s :=
  fun _ _ => ⟨rfl, fun _ _ => rfl⟩

private theorem watchPresAll_trans {c : PlainCfg} {s s1 s2 : PlainState}
    (h1 : WatchPresAll c s s1) (h2 : WatchPresAll c s1 s2) : WatchPresAll c s s2 := by
  intro l hl
  have ⟨hs1, he1⟩ := h1 l hl
  have ⟨hs2, he2⟩ := h2 l hl
  exact ⟨hs2.trans hs1, fun k hk => (he2 k (hs1 ▸ hk)).trans (he1 k hk)⟩

private theorem wvec_set_even_u {wvec : List (BitVec 32)} {l : Nat} {v : BitVec 32}
    (hl : 2 * l < wvec.length) (j : Nat) :
    (wvec.set (2 * l) v)[2 * j + 1]? = wvec[2 * j + 1]? ∧
    (j ≠ l → (wvec.set (2 * l) v)[2 * j]? = wvec[2 * j]?) ∧
    (wvec.set (2 * l) v)[2 * l]? = some v :=
  ⟨List.getElem?_set_ne (by omega), fun hne => List.getElem?_set_ne (by omega),
   List.getElem?_set_self hl⟩

private theorem wvec_set_odd_u {wvec : List (BitVec 32)} {l : Nat} {v : BitVec 32}
    (hl : 2 * l + 1 < wvec.length) (j : Nat) :
    (wvec.set (2 * l + 1) v)[2 * j]? = wvec[2 * j]? ∧
    (j ≠ l → (wvec.set (2 * l + 1) v)[2 * j + 1]? = wvec[2 * j + 1]?) ∧
    (wvec.set (2 * l + 1) v)[2 * l + 1]? = some v :=
  ⟨List.getElem?_set_ne (by omega), fun hne => List.getElem?_set_ne (by omega),
   List.getElem?_set_self hl⟩

private theorem wpush_sentinel_disjoint {c : PlainCfg} {s1 : PlainState} {lit cnt : Nat}
    (hlay : WatchStackLayout c s1) (hlit : lit < 2 * c.mv) (hc12 : cnt = 1 ∨ cnt = 2)
    (hs0 : s1.wstk[watchOff s1 lit + watchSize s1 lit]? = some 0xFFFFFFFF#32)
    (hs1 : cnt = 2 → s1.wstk[watchOff s1 lit + watchSize s1 lit + 1]? = some 0xFFFFFFFF#32) :
    ∀ j < 2 * c.mv, j ≠ lit → 0 < watchSize s1 j →
      watchOff s1 j + watchSize s1 j ≤ watchOff s1 lit ∨
      watchOff s1 lit + (watchSize s1 lit + cnt) ≤ watchOff s1 j := by
  intro j hj hne hszj
  by_cases h1 : watchOff s1 j + watchSize s1 j ≤ watchOff s1 lit
  · exact Or.inl h1
  by_cases h2 : watchOff s1 lit + (watchSize s1 lit + cnt) ≤ watchOff s1 j
  · exact Or.inr h2
  exfalso
  have hbad2 : watchOff s1 j = watchOff s1 lit + watchSize s1 lit + 1 → cnt = 2 → False :=
    fun heq hc2 => by
      have hns := hlay.no_sentinel j hj 0 hszj; rw [Nat.add_zero, heq] at hns; exact hns (hs1 hc2)
  by_cases hszl : 0 < watchSize s1 lit
  · rcases hlay.disjoint j lit hj hlit hne hszj hszl with hd | hd
    · exact h1 hd
    by_cases heq : watchOff s1 j = watchOff s1 lit + watchSize s1 lit
    · have hns := hlay.no_sentinel j hj 0 hszj; rw [Nat.add_zero, heq] at hns; exact hns hs0
    · exact hbad2 (by omega) (by omega)
  · by_cases hle : watchOff s1 j ≤ watchOff s1 lit
    · have hns := hlay.no_sentinel j hj (watchOff s1 lit - watchOff s1 j) (by omega)
      rw [show watchOff s1 j + (watchOff s1 lit - watchOff s1 j) =
        watchOff s1 lit + watchSize s1 lit by omega] at hns; exact hns hs0
    · exact hbad2 (by omega) (by omega)

private theorem wpush_finalize {c : PlainCfg} {s s2 : PlainState} {lit cnt dst wlen' : Nat}
    {w0 w1 : BitVec 32} {wvec' wstk' wsort' : List (BitVec 32)}
    (hlay2 : WatchStackLayout c s2) (hpres : WatchPresAll c s s2)
    (hlit : lit < 2 * c.mv) (hc12 : cnt = 1 ∨ cnt = 2)
    (hw0 : cnt = 1 → w0 ≠ 0xFFFFFFFF#32)
    (hw1 : cnt = 2 → w0 ≠ 0xFFFFFFFF#32 ∧ w1 ≠ 0xFFFFFFFF#32)
    (hwlen_le : s2.wlen ≤ wlen') (hdst1 : 1 ≤ dst)
    (hdst_le : dst + (wSz s2.wvec lit + cnt) ≤ wlen')
    (hother_wv : ∀ j < 2 * c.mv, j ≠ lit →
      wOff wvec' j = wOff s2.wvec j ∧ wSz wvec' j = wSz s2.wvec j)
    (hlit_off : wOff wvec' lit = dst) (hlit_sz : wSz wvec' lit = wSz s2.wvec lit + cnt)
    (hdisj : ∀ j < 2 * c.mv, j ≠ lit → 0 < wSz s2.wvec j →
      wOff s2.wvec j + wSz s2.wvec j ≤ dst ∨ dst + (wSz s2.wvec lit + cnt) ≤ wOff s2.wvec j)
    (hother_st : ∀ j < 2 * c.mv, j ≠ lit → ∀ k < wSz s2.wvec j,
      wstk'[wOff s2.wvec j + k]? = s2.wstk[wOff s2.wvec j + k]?)
    (hcopy : ∀ k < wSz s2.wvec lit, wstk'[dst + k]? = s2.wstk[wOff s2.wvec lit + k]?)
    (hat0 : wstk'[dst + wSz s2.wvec lit]? = some w0)
    (hat1 : cnt = 2 → wstk'[dst + wSz s2.wvec lit + 1]? = some w1)
    (wusable' : BitVec 64) :
    let s' : PlainState :=
      { s with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable',
               heur := { s.heur with wsort := wsort' } }
    WatchStackLayout c s' ∧
    (∀ l < 2 * c.mv, l ≠ lit → watchSize s' l = watchSize s l ∧
      ∀ k < watchSize s l, s'.wstk[watchOff s' l + k]? = s.wstk[watchOff s l + k]?) ∧
    watchSize s' lit = watchSize s lit + cnt ∧
    (∀ k < watchSize s lit, s'.wstk[watchOff s' lit + k]? = s.wstk[watchOff s lit + k]?) ∧
    s'.wstk[watchOff s' lit + watchSize s lit]? = some w0 ∧
    (cnt = 2 → s'.wstk[watchOff s' lit + watchSize s lit + 1]? = some w1) := by
  intro s'
  have hoff_l : watchOff s' lit = dst := hlit_off
  have hsz_l : watchSize s' lit = wSz s2.wvec lit + cnt := hlit_sz
  have hoff_o : ∀ j < 2 * c.mv, j ≠ lit → watchOff s' j = watchOff s2 j :=
    fun j hj hne => (hother_wv j hj hne).1
  have hsz_o : ∀ j < 2 * c.mv, j ≠ lit → watchSize s' j = watchSize s2 j :=
    fun j hj hne => (hother_wv j hj hne).2
  have hsz_lit2 : wSz s2.wvec lit = watchSize s lit := (hpres lit hlit).1
  have hne0 : w0 ≠ 0xFFFFFFFF#32 := by rcases hc12 with rfl | rfl; exact hw0 rfl; exact (hw1 rfl).1
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, by rw [hsz_l, hsz_lit2], ?_, ?_, ?_⟩
  · intro l hl; by_cases hll : l = lit
    · rcases hll.symm with rfl; rw [hoff_l, hsz_l]; exact hdst_le
    · rw [hoff_o l hl hll, hsz_o l hl hll]; exact Nat.le_trans (hlay2.bounds l hl) hwlen_le
  · intro l hl hpos; by_cases hll : l = lit
    · rcases hll.symm with rfl; rw [hoff_l]; exact hdst1
    · rw [hsz_o l hl hll] at hpos; rw [hoff_o l hl hll]; exact hlay2.pos_off l hl hpos
  · intro l1 l2 h1 h2 hne hp1 hp2; by_cases hl1 : l1 = lit
    · rcases hl1.symm with rfl; have hl2 : l2 ≠ lit := hne.symm; rw [hsz_o l2 h2 hl2] at hp2
      rw [hoff_l, hsz_l, hoff_o l2 h2 hl2, hsz_o l2 h2 hl2]; exact (hdisj l2 h2 hl2 hp2).symm
    · by_cases hl2 : l2 = lit
      · rcases hl2.symm with rfl; rw [hsz_o l1 h1 hl1] at hp1
        rw [hoff_o l1 h1 hl1, hsz_o l1 h1 hl1, hoff_l, hsz_l]; exact hdisj l1 h1 hl1 hp1
      · rw [hsz_o l1 h1 hl1] at hp1; rw [hsz_o l2 h2 hl2] at hp2
        rw [hoff_o l1 h1 hl1, hsz_o l1 h1 hl1, hoff_o l2 h2 hl2, hsz_o l2 h2 hl2]
        exact hlay2.disjoint l1 l2 h1 h2 hne hp1 hp2
  · intro l hl k hk; by_cases hll : l = lit
    · rcases hll.symm with rfl; rw [hsz_l] at hk; rw [hoff_l]
      by_cases hks : k < wSz s2.wvec lit
      · change wstk'[dst + k]? ≠ _; rw [hcopy k hks]; exact hlay2.no_sentinel lit hlit k hks
      · by_cases hk0 : k = wSz s2.wvec lit
        · subst hk0; change wstk'[dst + wSz s2.wvec lit]? ≠ _; rw [hat0]
          exact fun heq => hne0 (Option.some.inj heq)
        · have hc2 : cnt = 2 := by omega
          have hk1 : k = wSz s2.wvec lit + 1 := by omega
          subst hk1; change wstk'[dst + (wSz s2.wvec lit + 1)]? ≠ _
          rw [← Nat.add_assoc, hat1 hc2]; exact fun heq => (hw1 hc2).2 (Option.some.inj heq)
    · rw [hsz_o l hl hll] at hk; rw [hoff_o l hl hll]; change wstk'[wOff s2.wvec l + k]? ≠ _
      rw [hother_st l hl hll k hk]; exact hlay2.no_sentinel l hl k hk
  · intro l hl hne; have ⟨hp1, hp2⟩ := hpres l hl
    have hp1' : wSz s2.wvec l = watchSize s l := hp1
    refine ⟨(hsz_o l hl hne).trans hp1, fun k hk => ?_⟩
    change wstk'[watchOff s' l + k]? = _
    rw [hoff_o l hl hne]; exact (hother_st l hl hne k (hp1' ▸ hk)).trans (hp2 k hk)
  · intro k hk; change wstk'[watchOff s' lit + k]? = _
    rw [hoff_l]; exact (hcopy k (hsz_lit2 ▸ hk)).trans ((hpres lit hlit).2 k hk)
  · change wstk'[watchOff s' lit + watchSize s lit]? = _; rw [hoff_l, ← hsz_lit2]; exact hat0
  · intro hc2; change wstk'[watchOff s' lit + watchSize s lit + 1]? = _
    rw [hoff_l, ← hsz_lit2]; exact hat1 hc2

private theorem wpush_getElem_toNat {xs : List (BitVec 32)} {i j : Nat}
    (hi : i < xs.length) (hij : i = j) : (xs[i]'hi).toNat = (xs[j]?.getD 0#32).toNat := by
  subst hij; rw [List.getElem?_eq_getElem hi, Option.getD_some]

private theorem bv64_lit2 {lit : Val i32} :
    (lit.setWidth 64 <<< (1 : Nat)).toNat = 2 * lit.toNat := by
  rw [BitVec.toNat_shiftLeft, zext_toNat _ (by decide)]; simp [Nat.shiftLeft_eq]; omega

private theorem bv64_lit2p1 {lit : Val i32} :
    ((lit.setWidth 64 <<< (1 : Nat)) + 1).toNat = 2 * lit.toNat + 1 := by
  rw [BitVec.toNat_add, bv64_lit2]; simp; omega

private theorem bv64_sub_ofNat {a b : Nat} (hle : b ≤ a) (ha : a < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b).toNat = a - b := by
  have h1 := bv64_ofNat_toNat (n := a) ha; have h2 := bv64_ofNat_toNat (n := b) (by omega); bv_omega

private theorem bv64_add_no_ovf {a b : BitVec 64} (h : a.toNat + b.toNat < 2 ^ 64) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt h

private theorem bv64_add1_no_ovf {a : BitVec 64} (h : a.toNat + 1 < 2 ^ 64) :
    (a + 1).toNat = a.toNat + 1 := bv64_add_no_ovf (by simpa using h)

private theorem bv32_trunc_ofNat {n : Nat} (h : n < 2 ^ 32) :
    ((BitVec.ofNat 64 n).setWidth 32).toNat = n := by
  rw [BitVec.toNat_setWidth, bv64_ofNat_toNat (by omega)]; exact Nat.mod_eq_of_lt h

private theorem bv32_trunc_add {a : BitVec 64} {b : Val i32} (h : a.toNat + b.toNat < 2 ^ 32) :
    ((a + b.setWidth 64).setWidth 32).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_add, zext_toNat _ (by decide),
    Nat.mod_eq_of_lt (by omega : a.toNat + b.toNat < 2 ^ 64), Nat.mod_eq_of_lt h]

private theorem bv64_eq_zero_of_not_pos {x : BitVec 64} (h : ¬ (0 < x.toNat)) : x = 0#64 :=
  BitVec.eq_of_toNat_eq (by simp; omega)

private theorem bv64_fit_of_not_ugt {wcap wlen : Nat} {x : BitVec 64}
    (hle : wlen ≤ wcap) (hcap : wcap < 2 ^ 64)
    (h : ¬ ((BitVec.ofNat 64 wcap - BitVec.ofNat 64 wlen).toNat < x.toNat)) :
    x.toNat ≤ wcap - wlen := by
  have := bv64_sub_ofNat hle hcap; omega

private theorem bv32_eq_nat {x : Val i32} (n : Nat) (hn : n < 2 ^ 32)
    (h : x = BitVec.ofNat 32 n) : x.toNat = n := by
  have := congrArg BitVec.toNat h; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at this; exact this

private theorem bv32_ne_nat {x : Val i32} (n : Nat) (hn : n < 2 ^ 32)
    (h : x ≠ BitVec.ofNat 32 n) : x.toNat ≠ n := fun heq =>
  h (BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]; exact heq))

private abbrev wpOp1 {t r : Ty} (code : OpCode [t] [r]) (a : Arg Val t) : Op Val [r] :=
  { sig := [t], code := code, args := (a, ()) }

private abbrev wpOp2 {t r : Ty} (code : OpCode [t, t] [r]) (a b : Arg Val t) : Op Val [r] :=
  { sig := [t, t], code := code, args := (a, b, ()) }

private abbrev eHdrLd (h : Val i64) (off : BitVec 64) (k : Val i64 → Expr Val Cont [Ty.bool]) :
    Expr Val Cont [Ty.bool] :=
  Expr.let_ (wpOp2 (.add i64) (Arg.var h) (Arg.imm off)) fun p => Expr.load i64 (Arg.var p.fst) k

private abbrev eHdrSt (h : Val i64) (off : BitVec 64) (v : Arg Val i64)
    (k : Expr Val Cont [Ty.bool]) : Expr Val Cont [Ty.bool] :=
  Expr.let_ (wpOp2 (.add i64) (Arg.var h) (Arg.imm off)) fun p =>
  Expr.store (t := i64) v (Arg.var p.fst) k

private abbrev eIdx4 (base idx : Val i64) (k : Val i64 → Expr Val Cont [Ty.bool]) :
    Expr Val Cont [Ty.bool] :=
  Expr.let_ (wpOp2 (.mul i64) (Arg.var idx) (Arg.imm 4)) fun p1 =>
  Expr.let_ (wpOp2 (.add i64) (Arg.var base) (Arg.var p1.fst)) fun p2 => k p2.fst

private abbrev eAddIdx4 (base a : Val i64) (b : Arg Val i64)
    (k : Val i64 → Expr Val Cont [Ty.bool]) : Expr Val Cont [Ty.bool] :=
  Expr.let_ (wpOp2 (.add i64) (Arg.var a) b) fun p => eIdx4 base p.fst k

private abbrev eLit2Addr (pWvec : Val i64) (lit : Val i32)
    (k : Val i64 → Expr Val Cont [Ty.bool]) : Expr Val Cont [Ty.bool] :=
  Expr.let_ (wpOp1 (.zext 32 64) (Arg.var lit)) fun p1 =>
  Expr.let_ (wpOp1 (.sext 32 64) (Arg.imm 1)) fun p2 =>
  Expr.let_ (wpOp2 (.shl i64) (Arg.var p1.fst) (Arg.var p2.fst)) fun p3 => eIdx4 pWvec p3.fst k

private abbrev eLit2p1Addr (pWvec : Val i64) (lit : Val i32)
    (k : Val i64 → Expr Val Cont [Ty.bool]) : Expr Val Cont [Ty.bool] :=
  Expr.let_ (wpOp1 (.zext 32 64) (Arg.var lit)) fun p1 =>
  Expr.let_ (wpOp1 (.sext 32 64) (Arg.imm 1)) fun p2 =>
  Expr.let_ (wpOp2 (.shl i64) (Arg.var p1.fst) (Arg.var p2.fst)) fun p3 =>
  eAddIdx4 pWvec p3.fst (Arg.imm 1) k

private abbrev WPushPost (c : PlainCfg) (s : PlainState) (R : Mem 64 → Prop)
    (lit w0 w1 cnt : Val i32) (Q : Post [Ty.bool]) : Prop :=
  ∀ (ok : Bool) (wvec' wstk' : List (BitVec 32)) (wlen' : Nat) (wusable' : BitVec 64)
      (wsort' : List (BitVec 32)) (m' : Mem 64),
    let s' : PlainState :=
      { s with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable',
               heur := { s.heur with wsort := wsort' } }
    s'.LengthsOk c → WatchStackLayout c s' →
    (∀ l < 2 * c.mv, l ≠ lit.toNat →
      watchSize s' l = watchSize s l ∧
      ∀ k < watchSize s l, s'.wstk[watchOff s' l + k]? = s.wstk[watchOff s l + k]?) →
    (ok = true → lit.toNat < 2 * c.mv ∧ (cnt.toNat = 1 ∨ cnt.toNat = 2) ∧
      watchSize s' lit.toNat = watchSize s lit.toNat + cnt.toNat ∧
      (∀ k < watchSize s lit.toNat,
        s'.wstk[watchOff s' lit.toNat + k]? = s.wstk[watchOff s lit.toNat + k]?) ∧
      s'.wstk[watchOff s' lit.toNat + watchSize s lit.toNat]? = some w0 ∧
      (cnt.toNat = 2 →
        s'.wstk[watchOff s' lit.toNat + watchSize s lit.toNat + 1]? = some w1)) →
    (ok = false →
      (lit.toNat < 2 * c.mv → watchSize s' lit.toNat = watchSize s lit.toNat ∧
        ∀ k < watchSize s lit.toNat,
          s'.wstk[watchOff s' lit.toNat + k]? = s.wstk[watchOff s lit.toNat + k]?) ∧
      (c.mv * 2 ≤ lit.toNat ∨ (cnt.toNat ≠ 1 ∧ cnt.toNat ≠ 2) ∨ s' = s ∨ wusable' = 0#64)) →
    (PlainMem c s' ⋆ R) m' → Q (ok, ()) m'

/-- Relocation tail (`Plain1.lean:351-369`) of `plain_watch_push`. -/
private abbrev wpushRelocExpr (h pWvec pWstk offD szD ncapD cVal : Val i64)
    (lit w0 w1 cnt : Val i32) : Expr Val Cont [Ty.bool] :=
  eHdrLd h 56 fun ld_5 =>
  Expr.group (sig := [[i64]]) (fun Js => Blocks.cons (fun (p_32 : Tup Val [i64]) =>
    Expr.let_ (wpOp2 (.cmp .ult i64 .bool rfl) (Arg.var p_32.fst) (Arg.var szD)) fun p_33 =>
    Expr.jnz (Arg.var p_33.fst)
      (eAddIdx4 pWstk ld_5 (Arg.var p_32.fst) fun p3 =>
       eAddIdx4 pWstk offD (Arg.var p_32.fst) fun p_36 =>
       Expr.load i32 (Arg.var p_36) fun ld_v =>
       Expr.store (t := i32) (Arg.var ld_v) (Arg.var p3)
         (eAddIdx4 pWstk offD (Arg.var p_32.fst) fun p6 =>
          Expr.store (t := i32) (Arg.imm 0xFFFFFFFF#32) (Arg.var p6)
            (Expr.let_ (wpOp2 (.add i64) (Arg.var p_32.fst) (Arg.imm 1)) fun p7 =>
             Expr.jump Js.fst (Arg.var p7.fst, ()))))
      (eAddIdx4 pWstk ld_5 (Arg.var szD) fun p_36 =>
       Expr.store (t := i32) (Arg.var w0) (Arg.var p_36)
         (Expr.group (sig := [[]]) (fun _JsW => Blocks.cons (fun (_ : Tup Val []) =>
            Expr.let_ (wpOp2 (.add i64) (Arg.var szD) (Arg.var cVal)) fun p_38 =>
            Expr.group (sig := [[i64]]) (fun JsF => Blocks.cons (fun (p_39 : Tup Val [i64]) =>
              Expr.let_ (wpOp2 (.cmp .ult i64 .bool rfl) (Arg.var p_39.fst) (Arg.var ncapD))
                fun p_40 =>
              Expr.jnz (Arg.var p_40.fst)
                (eAddIdx4 pWstk ld_5 (Arg.var p_39.fst) fun q3 =>
                 Expr.store (t := i32) (Arg.imm 0xFFFFFFFF#32) (Arg.var q3)
                   (Expr.let_ (wpOp2 (.add i64) (Arg.var p_39.fst) (Arg.imm 1)) fun q4 =>
                    Expr.jump JsF.fst (Arg.var q4.fst, ())))
                (eLit2Addr pWvec lit fun p_45 =>
                 Expr.let_ (wpOp1 (.trunc 64 32) (Arg.var ld_5)) fun p_46 =>
                 Expr.store (t := i32) (Arg.var p_46.fst) (Arg.var p_45)
                   (eLit2p1Addr pWvec lit fun p_52 =>
                    Expr.let_ (wpOp2 (.add i64) (Arg.var szD) (Arg.var cVal)) fun p_53 =>
                    Expr.let_ (wpOp1 (.trunc 64 32) (Arg.var p_53.fst)) fun p_54 =>
                    Expr.store (t := i32) (Arg.var p_54.fst) (Arg.var p_52)
                      (eHdrLd h 464 fun ld_wu =>
                       Expr.let_ (wpOp2 (.add i64) (Arg.var ld_wu) (Arg.var szD)) fun p_56 =>
                       Expr.let_ (wpOp2 (.add i64) (Arg.var szD) (Arg.var cVal)) fun p_57 =>
                       Expr.let_ (wpOp2 (.sub i64) (Arg.var ncapD) (Arg.var p_57.fst)) fun p_58 =>
                       Expr.let_ (wpOp2 (.add i64) (Arg.var p_56.fst) (Arg.var p_58.fst))
                         fun p_59 =>
                       eHdrSt h 464 (Arg.var p_59.fst)
                         (Expr.let_ (wpOp2 (.add i64) (Arg.var ld_5) (Arg.var ncapD)) fun p_61 =>
                          eHdrSt h 56 (Arg.var p_61.fst) (Expr.ret (Arg.imm true, ())))))))
              Blocks.nil) fun JsF => Expr.jump JsF.fst (Arg.var p_38.fst, ())) Blocks.nil)
            fun JsW =>
            Expr.let_ (wpOp2 (.cmp .eq i32 .bool rfl) (Arg.var cnt) (Arg.imm 2)) fun p_37 =>
            Expr.jnz (Arg.var p_37.fst)
              (Expr.let_ (wpOp2 (.add i64) (Arg.var ld_5) (Arg.var szD)) fun p_38 =>
               eAddIdx4 pWstk p_38.fst (Arg.imm 1) fun p_41 =>
               Expr.store (t := i32) (Arg.var w1) (Arg.var p_41) (Expr.jump JsW.fst ()))
              (Expr.jump JsW.fst ())))) Blocks.nil)
    fun Js => Expr.jump Js.fst (Arg.imm 0, ())

private theorem wpush_reloc_wp {Γ : Env} {Q : Post [Ty.bool]} {X : XPost} {c : PlainCfg}
    {s : PlainState} {R : Mem 64 → Prop} {wvecD wstkD wsortD : List (BitVec 32)} {wlenD : Nat}
    {wusD offD szD ncapD : BitVec 64} {lit w0 w1 cnt : Val i32} {mD : Mem 64}
    (hlit_lt : lit.toNat < 2 * c.mv) (hcnt12 : cnt.toNat = 1 ∨ cnt.toNat = 2)
    (hw0 : cnt.toNat = 1 → w0 ≠ 0xFFFFFFFF#32)
    (hw1 : cnt.toNat = 2 → w0 ≠ 0xFFFFFFFF#32 ∧ w1 ≠ 0xFFFFFFFF#32)
    (hwd1 : 1 ≤ wlenD)
    (hlenD : PlainState.LengthsOk c
      { s with wvec := wvecD, wstk := wstkD, wlen := wlenD, wusable := wusD,
               heur := { s.heur with wsort := wsortD } })
    (hlayD : WatchStackLayout c
      { s with wvec := wvecD, wstk := wstkD, wlen := wlenD, wusable := wusD,
               heur := { s.heur with wsort := wsortD } })
    (hpresD : WatchPresAll c s
      { s with wvec := wvecD, wstk := wstkD, wlen := wlenD, wusable := wusD,
               heur := { s.heur with wsort := wsortD } })
    (hoffD : offD.toNat = wOff wvecD lit.toNat) (hszD : szD.toNat = wSz wvecD lit.toNat)
    (hnc_ge : szD.toNat + cnt.toNat ≤ ncapD.toNat) (hnc_fit : ncapD.toNat ≤ c.wcap - wlenD)
    (hmD : (PlainMem c
      { s with wvec := wvecD, wstk := wstkD, wlen := wlenD, wusable := wusD,
               heur := { s.heur with wsort := wsortD } } ⋆ R) mD)
    (hQ : WPushPost c s R lit w0 w1 cnt Q) :
    wp Γ Q X (wpushRelocExpr c.hdr c.pWvec c.pWstk offD szD ncapD (cnt.setWidth 64) lit w0 w1 cnt)
      mD := by
  obtain hmv : c.mv < 2 ^ 28 := c.hmv; obtain hwcap : c.wcap < 2 * 2 ^ 28 := c.hwcap
  obtain hwvlD : wvecD.length = 4 * c.mv := hlenD.wvec_len
  obtain hwslD : wstkD.length = c.wcap := hlenD.wstk_len_arr
  obtain hwleD : wlenD ≤ c.wcap := hlenD.wlen_le; obtain hokD := hlenD.heur_ok
  obtain hlit2 := bv64_lit2 (lit := lit); obtain hlit2p1 := bv64_lit2p1 (lit := lit)
  obtain hoffD_le : offD.toNat + szD.toNat ≤ wlenD := by
    have hbl := hlayD.bounds lit.toNat hlit_lt
    change wOff wvecD lit.toNat + wSz wvecD lit.toNat ≤ wlenD at hbl; omega
  obtain hdst_eq : (BitVec.ofNat 64 wlenD).toNat = wlenD := bv64_ofNat_toNat (by omega)
  dsimp only [wpushRelocExpr, eHdrLd, eHdrSt, eIdx4, eAddIdx4, eLit2Addr, eLit2p1Addr]
  c0_to_group
  refine wp_loop_inv
    (fun (k, ()) mK => k.toNat ≤ szD.toNat ∧ ∃ wstkK : List (BitVec 32), wstkK.length = c.wcap ∧
      (∀ j < 2 * c.mv, j ≠ lit.toNat → ∀ r < wSz wvecD j,
        wstkK[wOff wvecD j + r]? = wstkD[wOff wvecD j + r]?) ∧
      (∀ r < k.toNat, wstkK[wlenD + r]? = wstkD[offD.toNat + r]?) ∧
      (∀ r, k.toNat ≤ r → r < szD.toNat → wstkK[offD.toNat + r]? = wstkD[offD.toNat + r]?) ∧
      (PlainMem c { s with wvec := wvecD, wstk := wstkK, wlen := wlenD, wusable := wusD,
                           heur := { s.heur with wsort := wsortD } } ⋆ R) mK)
    (fun (k, ()) _ => szD.toNat - k.toNat) (fun JK hLoopK => ?_) ?_
  · c0_steps; exact hLoopK _ _ ⟨by simp, wstkD, hwslD, fun _ _ _ _ _ => rfl,
      fun _ hr => by simp at hr, fun _ _ _ => rfl, hmD⟩
  · rintro JK ⟨k, ⟨⟩⟩ mK ⟨hk_le, wstkK, hwsK, hothK, hcopK, hsrcK, hmK⟩ hLoopK; clear hmD
    c0_to_group
    · have hk_lt : k.toNat < szD.toNat := by c0_bound
      have hkp1 : (k + 1).toNat = k.toNat + 1 := bv64_add1_no_ovf (by omega)
      have hdk : (BitVec.ofNat 64 wlenD + k).toNat = wlenD + k.toNat := by
        rw [BitVec.toNat_add, hdst_eq]; omega
      have hok_eq : (offD + k).toNat = offD.toNat + k.toNat := bv64_add_no_ovf (by omega)
      c0_steps
      refine hLoopK _ _ (by dsimp only; omega)
        ⟨by omega, _, by rw [List.length_set, List.length_set, hwsK], ?_, ?_, ?_, hm⟩
      · intro j hj hne r hr
        have hbj := hlayD.bounds j hj; change wOff wvecD j + wSz wvecD j ≤ wlenD at hbj
        have hdj := hlayD.disjoint j lit.toNat hj hlit_lt hne
          (by change 0 < wSz wvecD j; omega) (by change 0 < wSz wvecD lit.toNat; omega)
        change wOff wvecD j + wSz wvecD j ≤ wOff wvecD lit.toNat ∨
          wOff wvecD lit.toNat + wSz wvecD lit.toNat ≤ wOff wvecD j at hdj
        rw [List.getElem?_set_ne (by rw [hok_eq]; rcases hdj with hd | hd <;> omega),
            List.getElem?_set_ne (by rw [hdk]; omega)]; exact hothK j hj hne r hr
      · intro r hr; by_cases hrk : r = k.toNat
        · subst hrk; rw [List.getElem?_set_ne (by rw [hok_eq]; omega), ← hdk,
            List.getElem?_set_self (by rw [hdk]; omega), ← List.getElem?_eq_getElem (by omega),
            hok_eq]; exact hsrcK k.toNat (by omega) hk_lt
        · rw [List.getElem?_set_ne (by rw [hok_eq]; omega),
            List.getElem?_set_ne (by rw [hdk]; omega)]; exact hcopK r (by omega)
      · intro r hr1 hr2
        rw [List.getElem?_set_ne (by rw [hok_eq]; omega),
            List.getElem?_set_ne (by rw [hdk]; omega)]; exact hsrcK r (by omega) hr2
    · have hk_eq : k.toNat = szD.toNat := by
        have : ¬ (k.toNat < szD.toNat) := by c0_bound
        omega
      clear hLoopK JK hsrcK
      obtain hdsz : (BitVec.ofNat 64 wlenD + szD).toNat = wlenD + szD.toNat := by
        rw [BitVec.toNat_add, hdst_eq]; omega
      obtain hdszp1 : ((BitVec.ofNat 64 wlenD + szD) + 1).toNat = wlenD + szD.toNat + 1 := by
        rw [BitVec.toNat_add, hdsz]; simp; omega
      c0_to_group
      refine wp_join_group
        (fun _ mW => ∃ wstkW : List (BitVec 32), wstkW.length = c.wcap ∧
          (∀ idx < wlenD, wstkW[idx]? = wstkK[idx]?) ∧
          (∀ r < szD.toNat, wstkW[wlenD + r]? = wstkD[offD.toNat + r]?) ∧
          wstkW[wlenD + szD.toNat]? = some w0 ∧
          (cnt.toNat = 2 → wstkW[wlenD + szD.toNat + 1]? = some w1) ∧
          (PlainMem c { s with wvec := wvecD, wstk := wstkW, wlen := wlenD, wusable := wusD,
                               heur := { s.heur with wsort := wsortD } } ⋆ R) mW) ?_ ?_
      · rintro _ _ mW ⟨wstkW, hwsW, hpreW, hcopW, hat0W, hat1W, hmW⟩; clear hwsK hcopK
        c0_to_group
        refine wp_loop_inv
          (fun (kf, ()) mF => szD.toNat + cnt.toNat ≤ kf.toNat ∧ kf.toNat ≤ ncapD.toNat ∧
            ∃ wstkF : List (BitVec 32), wstkF.length = c.wcap ∧
              (∀ idx < wlenD + szD.toNat + cnt.toNat, wstkF[idx]? = wstkW[idx]?) ∧
              (PlainMem c { s with wvec := wvecD, wstk := wstkF, wlen := wlenD, wusable := wusD,
                                   heur := { s.heur with wsort := wsortD } } ⋆ R) mF)
          (fun (kf, ()) _ => ncapD.toNat - kf.toNat) (fun JF hLoopF => ?_) ?_
        · c0_steps
          have hsc : (szD + cnt.setWidth 64).toNat = szD.toNat + cnt.toNat := by
            rw [BitVec.toNat_add, zext_toNat _ (by decide)]; omega
          exact hLoopF _ _ ⟨by omega, by omega, wstkW, hwsW, fun _ _ => rfl, hmW⟩
        · rintro JF ⟨kf, ⟨⟩⟩ mF ⟨hkf_ge, hkf_le, wstkF, hwsF, hpreF, hmF⟩ hLoopF; clear hmW
          c0_steps
          · have hkf_lt : kf.toNat < ncapD.toNat := by c0_bound
            have hdkf : (BitVec.ofNat 64 wlenD + kf).toNat = wlenD + kf.toNat := by
              rw [BitVec.toNat_add, hdst_eq]; omega
            have hkfp1 : (kf + 1).toNat = kf.toNat + 1 := bv64_add1_no_ovf (by omega)
            refine hLoopF _ _ (by dsimp only; omega)
              ⟨by omega, by omega, _, by rw [List.length_set, hwsF], fun idx hidx => by
                rw [hdkf, List.getElem?_set_ne (by omega)]; exact hpreF idx hidx, hm⟩
          · have hdst32 := bv32_trunc_ofNat (n := wlenD) (by omega)
            have hsz32 := bv32_trunc_add (a := szD) (b := cnt) (by omega)
            have hwlen_new : (BitVec.ofNat 64 wlenD + ncapD).toNat = wlenD + ncapD.toNat := by
              rw [BitVec.toNat_add, hdst_eq]; omega
            have hev := wvec_set_even_u (wvec := wvecD) (l := lit.toNat)
              (v := (BitVec.ofNat 64 wlenD).setWidth 32) (by omega)
            have hod := wvec_set_odd_u (wvec := wvecD.set (2 * lit.toNat)
                ((BitVec.ofNat 64 wlenD).setWidth 32)) (l := lit.toNat)
              (v := (szD + cnt.setWidth 64).setWidth 32) (by rw [List.length_set]; omega)
            have hfin := wpush_finalize (c := c) (s := s)
              (s2 := { s with wvec := wvecD, wstk := wstkD, wlen := wlenD, wusable := wusD,
                              heur := { s.heur with wsort := wsortD } })
              (lit := lit.toNat) (cnt := cnt.toNat) (dst := wlenD)
              (wlen' := (BitVec.ofNat 64 wlenD + ncapD).toNat)
              (wvec' := (wvecD.set (lit.setWidth 64 <<< (1 : Nat)).toNat
                  ((BitVec.ofNat 64 wlenD).setWidth 32)).set
                  ((lit.setWidth 64 <<< (1 : Nat) + 1).toNat)
                  ((szD + cnt.setWidth 64).setWidth 32))
              (wstk' := wstkF) (wsort' := wsortD) hlayD hpresD hlit_lt hcnt12 hw0 hw1
              (by dsimp only; omega) hwd1 (by dsimp only; omega)
              (fun j hj hne => by
                rw [wOff, wSz, hlit2, hlit2p1, (hod j).1, (hev j).2.1 hne, (hod j).2.1 hne,
                  (hev j).1]; exact ⟨rfl, rfl⟩)
              (by rw [wOff, hlit2, hlit2p1, (hod lit.toNat).1, (hev lit.toNat).2.2,
                Option.getD_some, hdst32])
              (by rw [wSz, hlit2, hlit2p1, (hod lit.toNat).2.2, Option.getD_some, hsz32, hszD])
              (fun j hj _ _ => Or.inl (hlayD.bounds j hj))
              (fun j hj hne r hr => by
                have hbj := hlayD.bounds j hj; change wOff wvecD j + wSz wvecD j ≤ wlenD at hbj
                dsimp only at hr ⊢; rw [hpreF _ (by omega), hpreW _ (by omega)]
                exact hothK j hj hne r hr)
              (fun r hr => by
                dsimp only at hr ⊢; rw [hpreF _ (by omega), hcopW r (by omega), hoffD])
              (by dsimp only; rw [hpreF _ (by omega), ← hszD]; exact hat0W)
              (fun hc2 => by dsimp only; rw [hpreF _ (by omega), ← hszD]; exact hat1W hc2)
              (wusD + szD + (ncapD - (szD + cnt.setWidth 64)))
            exact hQ true _ wstkF _ _ wsortD _
              { hlenD with wvec_len := by rw [List.length_set, List.length_set, hwvlD],
                           wstk_len_arr := hwsF, wlen_le := by dsimp only; omega, heur_ok := hokD }
              hfin.1 hfin.2.1 (fun _ => ⟨hlit_lt, hcnt12, hfin.2.2.1, hfin.2.2.2.1,
                hfin.2.2.2.2.1, hfin.2.2.2.2.2⟩) (fun h => by cases h) hm
      · intro JW hJW; clear hQ hothK hlenD hlayD hpresD hokD; c0_split
        · obtain hc2 := bv32_eq_nat 2 (by decide) hc; c0_steps
          refine hJW _ _ ⟨_, by rw [List.length_set, List.length_set, hwsK],
            fun idx hidx => by
              rw [hdszp1, hdsz, List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)],
            fun r hr => by
              rw [hdszp1, hdsz, List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
              exact hcopK r (by omega),
            by rw [hdszp1, hdsz, List.getElem?_set_ne (by omega),
              List.getElem?_set_self (by omega)],
            fun _ => by rw [hdszp1, List.getElem?_set_self (by rw [List.length_set]; omega)], hm⟩
        · c0_steps; have hne2 := bv32_ne_nat 2 (by decide) hc
          refine hJW _ _ ⟨_, by rw [List.length_set, hwsK],
            fun idx hidx => by rw [hdsz, List.getElem?_set_ne (by omega)],
            fun r hr => by rw [hdsz, List.getElem?_set_ne (by omega)]; exact hcopK r (by omega),
            by rw [hdsz, List.getElem?_set_self (by omega)], fun hc2 => absurd hc2 hne2, hm⟩

/-- Case D (`Plain1.lean:340-370`: capacity growth, defrag/fallback/OOM, relocation). -/
private abbrev wpushCaseDExpr (h pWvec pWstk wcap off sz cVal : Val i64)
    (lit w0 w1 cnt : Val i32) : Expr Val Cont [Ty.bool] :=
  Expr.group (sig := [[i64]]) (fun _JsD1 => Blocks.cons (fun (p_28 : Tup Val [i64]) =>
    Expr.group (sig := [[i64]]) (fun _JsD2 => Blocks.cons (fun (p_29 : Tup Val [i64]) =>
      Expr.group (sig := [[i64, i64, i64]]) (fun _JsD3 => Blocks.cons
        (fun (p_30 : Tup Val [i64, i64, i64]) =>
          wpushRelocExpr h pWvec pWstk p_30.fst p_30.snd.fst p_30.snd.snd.fst cVal lit w0 w1 cnt)
        Blocks.nil) fun Js =>
      eHdrLd h 56 fun ld_5 =>
      Expr.let_ (wpOp2 (.sub i64) (Arg.var wcap) (Arg.var ld_5)) fun p_31 =>
      Expr.let_ (wpOp2 (.cmp .ugt i64 .bool rfl) (Arg.var p_29.fst) (Arg.var p_31.fst)) fun p_32 =>
      Expr.jnz (Arg.var p_32.fst)
        (Expr.group (sig := [[i64, i64]]) (fun _Js_1 => Blocks.cons
          (fun (p_33 : Tup Val [i64, i64]) =>
          Expr.group (sig := [[i64]]) (fun _Js_2 => Blocks.cons (fun (p_34 : Tup Val [i64]) =>
            eHdrLd h 56 fun ld1 =>
            Expr.let_ (wpOp2 (.sub i64) (Arg.var wcap) (Arg.var ld1)) fun p2 =>
            Expr.let_ (wpOp2 (.cmp .ugt i64 .bool rfl) (Arg.var p_34.fst) (Arg.var p2.fst))
              fun p3 =>
            Expr.jnz (Arg.var p3.fst) (Expr.ret (Arg.imm false, ()))
              (Expr.jump Js.fst (Arg.var p_33.fst, Arg.var p_33.snd.fst, Arg.var p_34.fst, ())))
            Blocks.nil) fun JsN =>
          eHdrLd h 56 fun ld1 =>
          Expr.let_ (wpOp2 (.sub i64) (Arg.var wcap) (Arg.var ld1)) fun p2 =>
          Expr.let_ (wpOp2 (.cmp .ugt i64 .bool rfl) (Arg.var p_29.fst) (Arg.var p2.fst)) fun p3 =>
          Expr.jnz (Arg.var p3.fst)
            (Expr.let_ (wpOp2 (.add i64) (Arg.var p_33.snd.fst) (Arg.var cVal)) fun p4 =>
             Expr.jump JsN.fst (Arg.var p4.fst, ()))
            (Expr.jump JsN.fst (Arg.var p_29.fst, ()))) Blocks.nil) fun JsE =>
         eHdrLd h 464 fun ld_6 =>
         Expr.let_ (wpOp2 (.cmp .ugt i64 .bool rfl) (Arg.var ld_6) (Arg.imm 0)) fun p_34 =>
         Expr.jnz (Arg.var p_34.fst)
           (Expr.call (as := [i64]) (bs := []) "plain_wstack_defrag" (Arg.var h, ()) fun _ =>
            eLit2Addr pWvec lit fun p_40 =>
            Expr.load i32 (Arg.var p_40) fun ld_7 =>
            Expr.let_ (wpOp1 (.zext 32 64) (Arg.var ld_7)) fun p_41 =>
            eLit2p1Addr pWvec lit fun q5 =>
            Expr.load i32 (Arg.var q5) fun ld8 =>
            Expr.let_ (wpOp1 (.zext 32 64) (Arg.var ld8)) fun q6 =>
            Expr.jump JsE.fst (Arg.var p_41.fst, Arg.var q6.fst, ()))
           (Expr.jump JsE.fst (Arg.var off, Arg.var sz, ())))
        (Expr.jump Js.fst (Arg.var off, Arg.var sz, Arg.var p_29.fst, ()))) Blocks.nil) fun JsN1 =>
    Expr.let_ (wpOp2 (.add i64) (Arg.var sz) (Arg.var cVal)) fun q1 =>
    Expr.let_ (wpOp2 (.cmp .ult i64 .bool rfl) (Arg.var p_28.fst) (Arg.var q1.fst)) fun q2 =>
    Expr.jnz (Arg.var q2.fst)
      (Expr.let_ (wpOp2 (.add i64) (Arg.var sz) (Arg.var cVal)) fun q3 =>
       Expr.jump JsN1.fst (Arg.var q3.fst, ()))
      (Expr.jump JsN1.fst (Arg.var p_28.fst, ()))) Blocks.nil) fun JsN0 =>
  Expr.let_ (wpOp2 (.cmp .eq i64 .bool rfl) (Arg.var sz) (Arg.imm 0)) fun q1 =>
  Expr.jnz (Arg.var q1.fst) (Expr.jump JsN0.fst (Arg.imm 2, ()))
    (Expr.let_ (wpOp1 (.sext 32 64) (Arg.imm 1)) fun q2 =>
     Expr.let_ (wpOp2 (.shl i64) (Arg.var sz) (Arg.var q2.fst)) fun q3 =>
     Expr.jump JsN0.fst (Arg.var q3.fst, ()))

private theorem wpush_caseD_wp {Γ : Env}
    (hDefrag : ∀ a m Q X, plainWstackDefragSpec a m Q X →
      Γ "plain_wstack_defrag" [i64] [] a m Q X)
    {Q : Post [Ty.bool]} {X : XPost} {c : PlainCfg} {s : PlainState} {R : Mem 64 → Prop}
    {wstk1 : List (BitVec 32)} {wlen1 : Nat} {off32 sz32 lit w0 w1 cnt : Val i32} {m1 : Mem 64}
    (hlit_lt : lit.toNat < 2 * c.mv) (hcnt12 : cnt.toNat = 1 ∨ cnt.toNat = 2)
    (hw0 : cnt.toNat = 1 → w0 ≠ 0xFFFFFFFF#32)
    (hw1 : cnt.toNat = 2 → w0 ≠ 0xFFFFFFFF#32 ∧ w1 ≠ 0xFFFFFFFF#32)
    (hw1_pos : 1 ≤ wlen1)
    (hlen1 : PlainState.LengthsOk c { s with wstk := wstk1, wlen := wlen1 })
    (hlay1 : WatchStackLayout c { s with wstk := wstk1, wlen := wlen1 })
    (hpres1 : WatchPresAll c s { s with wstk := wstk1, wlen := wlen1 })
    (hoff1 : off32.toNat = wOff s.wvec lit.toNat) (hsz1 : sz32.toNat = wSz s.wvec lit.toNat)
    (hm1 : (PlainMem c { s with wstk := wstk1, wlen := wlen1 } ⋆ R) m1)
    (hQ : WPushPost c s R lit w0 w1 cnt Q) :
    wp Γ Q X (wpushCaseDExpr c.hdr c.pWvec c.pWstk (BitVec.ofNat 64 c.wcap)
      (off32.setWidth 64) (sz32.setWidth 64) (cnt.setWidth 64) lit w0 w1 cnt) m1 := by
  obtain hmv : c.mv < 2 ^ 28 := c.hmv; obtain hwcap : c.wcap < 2 * 2 ^ 28 := c.hwcap
  obtain hwle1 : wlen1 ≤ c.wcap := hlen1.wlen_le
  obtain hlit2 := bv64_lit2 (lit := lit); obtain hlit2p1 := bv64_lit2p1 (lit := lit)
  obtain hoff1_le : wOff s.wvec lit.toNat + wSz s.wvec lit.toNat ≤ wlen1 :=
    hlay1.bounds lit.toNat hlit_lt
  dsimp only [wpushCaseDExpr, eHdrLd, eHdrSt, eIdx4, eAddIdx4, eLit2Addr, eLit2p1Addr]
  refine wp_join_group (fun (ncap0, ()) mN0 => ncap0.toNat < 2 ^ 30 ∧ m1 = mN0) ?_ ?_
  · rintro _ ⟨ncap0, ⟨⟩⟩ mN0 ⟨hnc0_lt, hmN0⟩; rcases hmN0 with rfl; c0_to_group
    refine wp_join_group (fun (ncap1, ()) mN1 =>
      wSz s.wvec lit.toNat + cnt.toNat ≤ ncap1.toNat ∧ ncap1.toNat < 2 ^ 30 ∧ m1 = mN1) ?_ ?_
    · rintro _ ⟨ncap1, ⟨⟩⟩ mN1 ⟨hnc1_ge, hnc1_lt, hmN1⟩; rcases hmN1 with rfl; c0_to_group
      refine wp_join_group (fun (offD, szD, ncapD, ()) mD =>
        ∃ (wvecD wstkD wsortD : List (BitVec 32)) (wlenD : Nat) (wusD : BitVec 64),
          let sD : PlainState :=
            { s with wvec := wvecD, wstk := wstkD, wlen := wlenD, wusable := wusD,
                     heur := { s.heur with wsort := wsortD } }
          1 ≤ wlenD ∧ sD.LengthsOk c ∧ WatchStackLayout c sD ∧ WatchPresAll c s sD ∧
          offD.toNat = wOff wvecD lit.toNat ∧ szD.toNat = wSz wvecD lit.toNat ∧
          szD.toNat + cnt.toNat ≤ ncapD.toNat ∧ ncapD.toNat ≤ c.wcap - wlenD ∧
          (PlainMem c sD ⋆ R) mD) ?_ ?_
      · rintro _ ⟨offD, szD, ncapD, ⟨⟩⟩ mD ⟨wvecD, wstkD, wsortD, wlenD, wusD, hwd1, hlenD, hlayD,
          hpresD, hoffD, hszD, hnc_ge, hnc_fit, hmD⟩
        exact wpush_reloc_wp hlit_lt hcnt12 hw0 hw1 hwd1 hlenD hlayD hpresD hoffD hszD
          hnc_ge hnc_fit hmD hQ
      · intro JD hJD; c0_to_group
        · refine wp_join_group (fun (offE, szE, ()) mE =>
            ∃ (wvecE wstkE wsortE : List (BitVec 32)) (wlenE : Nat),
              let sE : PlainState :=
                { s with wvec := wvecE, wstk := wstkE, wlen := wlenE, wusable := 0#64,
                         heur := { s.heur with wsort := wsortE } }
              1 ≤ wlenE ∧ sE.LengthsOk c ∧ WatchStackLayout c sE ∧ WatchPresAll c s sE ∧
              offE.toNat = wOff wvecE lit.toNat ∧ szE.toNat = wSz wvecE lit.toNat ∧
              (PlainMem c sE ⋆ R) mE) ?_ ?_
          · rintro _ ⟨offE, szE, ⟨⟩⟩ mE ⟨wvecE, wstkE, wsortE, wlenE, hwe1, hlenE, hlayE, hpresE,
              hoffE, hszE, hmE⟩
            obtain hwleE : wlenE ≤ c.wcap := hlenE.wlen_le
            obtain hszE_eq : szE.toNat = wSz s.wvec lit.toNat := by
              have h1 := (hpresE lit.toNat hlit_lt).1
              change wSz wvecE lit.toNat = wSz s.wvec lit.toNat at h1; omega
            clear hm1 hlen1 hlay1 hpres1; c0_to_group
            refine wp_join_group (fun (ncapE, ()) mN =>
              szE.toNat + cnt.toNat ≤ ncapE.toNat ∧ ncapE.toNat < 2 ^ 30 ∧ mE = mN) ?_ ?_
            · rintro _ ⟨ncapE, ⟨⟩⟩ mN ⟨hncE_ge, hncE_lt, hmN⟩; rcases hmN with rfl; c0_steps
              · exact hQ false wvecE wstkE wlenE 0#64 wsortE mE hlenE hlayE
                  (fun l hl _ => hpresE l hl) (fun h => by cases h)
                  (fun _ => ⟨fun hl => hpresE lit.toNat hl, Or.inr (Or.inr (Or.inr rfl))⟩) hmE
              · exact hJD _ _ ⟨wvecE, wstkE, wsortE, wlenE, 0#64, hwe1, hlenE, hlayE, hpresE,
                  hoffE, hszE, hncE_ge, bv64_fit_of_not_ugt hwleE (by omega) (by c0_bound), hmE⟩
            · intro JN hJN; clear hQ hJD hlenE hlayE hpresE; c0_steps
              · have hsc : (szE + cnt.setWidth 64).toNat = szE.toNat + cnt.toNat := by
                  rw [BitVec.toNat_add, zext_toNat _ (by decide)]; omega
                exact hJN _ _ ⟨by omega, by omega, rfl⟩
              · exact hJN _ _ ⟨by omega, hnc1_lt, rfl⟩
          · intro JE hJE; clear hQ hJD; c0_to_group
            · c0_call hDefrag; refine ⟨c, _, R, rfl, hlen1, hlay1, hm1, ?_⟩
              intro wvecE wstkE wlenE wsortE mE; dsimp only; intro hlenE hlayE h1E hpresE hmE
              obtain hwvlE : wvecE.length = 4 * c.mv := hlenE.wvec_len
              obtain hlit2_ltE : (lit.setWidth 64 <<< (1 : Nat)).toNat < wvecE.length := by omega
              obtain hlit2p1_ltE : ((lit.setWidth 64 <<< (1 : Nat)) + 1).toNat < wvecE.length := by
                omega
              c0_steps
              exact hJE _ _ ⟨wvecE, wstkE, wsortE, wlenE, h1E hw1_pos, hlenE, hlayE,
                watchPresAll_trans hpres1 hpresE,
                by rw [zext_toNat _ (by decide)]; exact wpush_getElem_toNat hlit2_ltE hlit2,
                by rw [zext_toNat _ (by decide)]; exact wpush_getElem_toNat hlit2p1_ltE hlit2p1,
                hmE⟩
            · have hus0 : s.wusable = 0#64 := bv64_eq_zero_of_not_pos (by c0_bound)
              have hm1' : (PlainMem c
                { s with wvec := s.wvec, wstk := wstk1, wlen := wlen1, wusable := 0#64,
                         heur := { s.heur with wsort := s.heur.wsort } } ⋆ R) m1 := by
                rw [← hus0]; exact hm1
              exact hJE _ _ ⟨s.wvec, wstk1, s.heur.wsort, wlen1, hw1_pos,
                { hlen1 with wlen_le := hlen1.wlen_le }, hlay1.with_wstk rfl rfl rfl, hpres1,
                by rw [zext_toNat _ (by decide)]; exact hoff1,
                by rw [zext_toNat _ (by decide)]; exact hsz1, hm1'⟩
        · exact hJD _ _ ⟨s.wvec, wstk1, s.heur.wsort, wlen1, s.wusable, hw1_pos, hlen1, hlay1,
            hpres1, by rw [zext_toNat _ (by decide)]; exact hoff1,
            by rw [zext_toNat _ (by decide)]; exact hsz1,
            by rw [zext_toNat _ (by decide), hsz1]; exact hnc1_ge,
            bv64_fit_of_not_ugt hwle1 (by omega) (by c0_bound), hm1⟩
    · intro JN1 hJN1; clear hQ; c0_steps
      · have hsc : (sz32.setWidth 64 + cnt.setWidth 64).toNat =
            wSz s.wvec lit.toNat + cnt.toNat := by
          rw [BitVec.toNat_add, zext_toNat _ (by decide), zext_toNat _ (by decide), hsz1]; omega
        exact hJN1 _ _ ⟨by omega, by omega, rfl⟩
      · have hsc : (sz32.setWidth 64 + cnt.setWidth 64).toNat =
            wSz s.wvec lit.toNat + cnt.toNat := by
          rw [BitVec.toNat_add, zext_toNat _ (by decide), zext_toNat _ (by decide), hsz1]; omega
        have : ¬ (ncap0.toNat < (sz32.setWidth 64 + cnt.setWidth 64).toNat) := by c0_bound
        exact hJN1 _ _ ⟨by omega, hnc0_lt, rfl⟩
  · intro JN0 hJN0; clear hQ; c0_steps
    · exact hJN0 _ _ ⟨by simp, rfl⟩
    · have hsh : (sz32.setWidth 64 <<< (1 : Nat)).toNat = 2 * wSz s.wvec lit.toNat := by
        rw [BitVec.toNat_shiftLeft, zext_toNat _ (by decide), hsz1]; simp [Nat.shiftLeft_eq]; omega
      exact hJN0 _ _ ⟨by omega, rfl⟩

/-- Case A (`Plain1.lean:312-322`: first allocation for a literal with `sz == 0 && off == 0`). -/
private abbrev wpushCaseAExpr (h pWvec pWstk wcap cVal : Val i64)
    (lit w0 w1 cnt : Val i32) : Expr Val Cont [Ty.bool] :=
  Expr.group (sig := [[]]) (fun _JsA => Blocks.cons (fun (_ : Tup Val []) =>
    eHdrLd h 56 fun ld_5 =>
    eIdx4 pWstk ld_5 fun p_29 =>
    Expr.store (t := i32) (Arg.var w0) (Arg.var p_29)
      (Expr.group (sig := [[]]) (fun _JsW => Blocks.cons (fun (_ : Tup Val []) =>
        eLit2Addr pWvec lit fun p_35 =>
        Expr.let_ (wpOp1 (.trunc 64 32) (Arg.var ld_5)) fun p_36 =>
        Expr.store (t := i32) (Arg.var p_36.fst) (Arg.var p_35)
          (eLit2p1Addr pWvec lit fun p_42 =>
           Expr.store (t := i32) (Arg.var cnt) (Arg.var p_42)
             (Expr.let_ (wpOp2 (.add i64) (Arg.var ld_5) (Arg.var cVal)) fun p_43 =>
              eHdrSt h 56 (Arg.var p_43.fst) (Expr.ret (Arg.imm true, ()))))) Blocks.nil)
        fun JsW =>
        Expr.let_ (wpOp2 (.cmp .eq i32 .bool rfl) (Arg.var cnt) (Arg.imm 2)) fun p_30 =>
        Expr.jnz (Arg.var p_30.fst)
          (eAddIdx4 pWstk ld_5 (Arg.imm 1) fun p_33 =>
           Expr.store (t := i32) (Arg.var w1) (Arg.var p_33) (Expr.jump JsW.fst ()))
          (Expr.jump JsW.fst ()))) Blocks.nil) fun Js =>
  eHdrLd h 56 fun ld =>
  Expr.let_ (wpOp2 (.sub i64) (Arg.var wcap) (Arg.var ld)) fun p_27 =>
  Expr.let_ (wpOp2 (.cmp .ugt i64 .bool rfl) (Arg.var cVal) (Arg.var p_27.fst)) fun p_28 =>
  Expr.jnz (Arg.var p_28.fst)
    (Expr.group (sig := [[]]) (fun _Js_1 => Blocks.cons (fun (_ : Tup Val []) =>
      eHdrLd h 56 fun ld1 =>
      Expr.let_ (wpOp2 (.sub i64) (Arg.var wcap) (Arg.var ld1)) fun p2 =>
      Expr.let_ (wpOp2 (.cmp .ugt i64 .bool rfl) (Arg.var cVal) (Arg.var p2.fst)) fun p3 =>
      Expr.jnz (Arg.var p3.fst) (Expr.ret (Arg.imm false, ())) (Expr.jump Js.fst ())) Blocks.nil)
      fun JsD =>
      eHdrLd h 464 fun ld2 =>
      Expr.let_ (wpOp2 (.cmp .ugt i64 .bool rfl) (Arg.var ld2) (Arg.imm 0)) fun p_30 =>
      Expr.jnz (Arg.var p_30.fst)
        (Expr.call (as := [i64]) (bs := []) "plain_wstack_defrag" (Arg.var h, ()) fun _ =>
         Expr.jump JsD.fst ())
        (Expr.jump JsD.fst ()))
    (Expr.jump Js.fst ())

private theorem wpush_caseA_wp {Γ : Env}
    (hDefrag : ∀ a m Q X, plainWstackDefragSpec a m Q X →
      Γ "plain_wstack_defrag" [i64] [] a m Q X)
    {Q : Post [Ty.bool]} {X : XPost} {c : PlainCfg} {s : PlainState} {R : Mem 64 → Prop}
    {wstk1 : List (BitVec 32)} {wlen1 : Nat} {lit w0 w1 cnt : Val i32} {m1 : Mem 64}
    (hlit_lt : lit.toNat < 2 * c.mv) (hcnt12 : cnt.toNat = 1 ∨ cnt.toNat = 2)
    (hw0 : cnt.toNat = 1 → w0 ≠ 0xFFFFFFFF#32)
    (hw1 : cnt.toNat = 2 → w0 ≠ 0xFFFFFFFF#32 ∧ w1 ≠ 0xFFFFFFFF#32)
    (hw1_pos : 1 ≤ wlen1) (hsz0 : wSz s.wvec lit.toNat = 0)
    (hlen1 : PlainState.LengthsOk c { s with wstk := wstk1, wlen := wlen1 })
    (hlay1 : WatchStackLayout c { s with wstk := wstk1, wlen := wlen1 })
    (hpres1 : WatchPresAll c s { s with wstk := wstk1, wlen := wlen1 })
    (hm1 : (PlainMem c { s with wstk := wstk1, wlen := wlen1 } ⋆ R) m1)
    (hQ : WPushPost c s R lit w0 w1 cnt Q) :
    wp Γ Q X (wpushCaseAExpr c.hdr c.pWvec c.pWstk (BitVec.ofNat 64 c.wcap)
      (cnt.setWidth 64) lit w0 w1 cnt) m1 := by
  obtain hmv : c.mv < 2 ^ 28 := c.hmv; obtain hwcap : c.wcap < 2 * 2 ^ 28 := c.hwcap
  obtain hwle1 : wlen1 ≤ c.wcap := hlen1.wlen_le
  obtain hlit2 := bv64_lit2 (lit := lit); obtain hlit2p1 := bv64_lit2p1 (lit := lit)
  dsimp only [wpushCaseAExpr, eHdrLd, eHdrSt, eIdx4, eAddIdx4, eLit2Addr, eLit2p1Addr]
  refine wp_join_group (fun _ mA =>
    ∃ (wvecA wstkA wsortA : List (BitVec 32)) (wlenA : Nat) (wusA : BitVec 64),
      let sA : PlainState :=
        { s with wvec := wvecA, wstk := wstkA, wlen := wlenA, wusable := wusA,
                 heur := { s.heur with wsort := wsortA } }
      1 ≤ wlenA ∧ cnt.toNat ≤ c.wcap - wlenA ∧ sA.LengthsOk c ∧ WatchStackLayout c sA ∧
      WatchPresAll c s sA ∧ (PlainMem c sA ⋆ R) mA) ?_ ?_
  · rintro _ _ mA ⟨wvecA, wstkA, wsortA, wlenA, wusA, hwa1, hwa_fit, hlenA, hlayA, hpresA, hmA⟩
    obtain hszA0 : wSz wvecA lit.toNat = 0 := by
      have h1 := (hpresA lit.toNat hlit_lt).1
      change wSz wvecA lit.toNat = wSz s.wvec lit.toNat at h1; omega
    clear hm1 hlen1 hlay1 hpres1 hw1_pos hwle1
    obtain hwvlA : wvecA.length = 4 * c.mv := hlenA.wvec_len
    obtain hwslA : wstkA.length = c.wcap := hlenA.wstk_len_arr
    obtain hwleA : wlenA ≤ c.wcap := hlenA.wlen_le; obtain hokA := hlenA.heur_ok
    obtain hpos_eq : (BitVec.ofNat 64 wlenA).toNat = wlenA := bv64_ofNat_toNat (by omega)
    obtain hpos_p1 : (BitVec.ofNat 64 wlenA + 1).toNat = wlenA + 1 := by
      rw [BitVec.toNat_add, hpos_eq]; simp; omega
    c0_to_group
    refine wp_join_group (fun _ mW => ∃ wstkW : List (BitVec 32), wstkW.length = c.wcap ∧
      (∀ idx < wlenA, wstkW[idx]? = wstkA[idx]?) ∧ wstkW[wlenA]? = some w0 ∧
      (cnt.toNat = 2 → wstkW[wlenA + 1]? = some w1) ∧
      (PlainMem c { s with wvec := wvecA, wstk := wstkW, wlen := wlenA, wusable := wusA,
                           heur := { s.heur with wsort := wsortA } } ⋆ R) mW) ?_ ?_
    · rintro _ _ mW ⟨wstkW, hwsW, hpreW, hat0W, hat1W, hmW⟩; clear hm; c0_steps
      have hpos32 := bv32_trunc_ofNat (n := wlenA) (by omega)
      have hnew_wlen : (BitVec.ofNat 64 wlenA + cnt.setWidth 64).toNat = wlenA + cnt.toNat := by
        rw [BitVec.toNat_add, hpos_eq, zext_toNat _ (by decide)]; omega
      have hev := wvec_set_even_u (wvec := wvecA) (l := lit.toNat)
        (v := (BitVec.ofNat 64 wlenA).setWidth 32) (by omega)
      have hod := wvec_set_odd_u (wvec := wvecA.set (2 * lit.toNat)
        ((BitVec.ofNat 64 wlenA).setWidth 32)) (l := lit.toNat) (v := cnt)
        (by rw [List.length_set]; omega)
      have hfin := wpush_finalize (c := c) (s := s)
        (s2 := { s with wvec := wvecA, wstk := wstkA, wlen := wlenA, wusable := wusA,
                        heur := { s.heur with wsort := wsortA } })
        (lit := lit.toNat) (cnt := cnt.toNat) (dst := wlenA)
        (wlen' := (BitVec.ofNat 64 wlenA + cnt.setWidth 64).toNat)
        (wvec' := (wvecA.set (lit.setWidth 64 <<< (1 : Nat)).toNat
            ((BitVec.ofNat 64 wlenA).setWidth 32)).set
            ((lit.setWidth 64 <<< (1 : Nat) + 1).toNat) cnt)
        (wstk' := wstkW) (wsort' := wsortA) hlayA hpresA hlit_lt hcnt12 hw0 hw1
        (by dsimp only; omega) hwa1 (by dsimp only; omega)
        (fun j hj hne => by
          rw [wOff, wSz, hlit2, hlit2p1, (hod j).1, (hev j).2.1 hne, (hod j).2.1 hne, (hev j).1]
          exact ⟨rfl, rfl⟩)
        (by rw [wOff, hlit2, hlit2p1, (hod lit.toNat).1, (hev lit.toNat).2.2,
          Option.getD_some, hpos32])
        (by rw [wSz, hlit2, hlit2p1, (hod lit.toNat).2.2, Option.getD_some, hszA0, Nat.zero_add])
        (fun j hj _ _ => Or.inl (hlayA.bounds j hj))
        (fun j hj _ k hk => by
          have hbj := hlayA.bounds j hj; change wOff wvecA j + wSz wvecA j ≤ wlenA at hbj
          dsimp only at hk ⊢; exact hpreW _ (by omega))
        (fun k hk => by dsimp only at hk; omega)
        (by dsimp only; rw [hszA0, Nat.add_zero]; exact hat0W)
        (fun hc2 => by dsimp only; rw [hszA0, Nat.add_zero]; exact hat1W hc2) wusA
      exact hQ true _ wstkW _ wusA wsortA _
        { hlenA with wvec_len := by rw [List.length_set, List.length_set, hwvlA],
                     wstk_len_arr := hwsW, wlen_le := by dsimp only; omega, heur_ok := hokA }
        hfin.1 hfin.2.1 (fun _ => ⟨hlit_lt, hcnt12, hfin.2.2.1, hfin.2.2.2.1,
          hfin.2.2.2.2.1, hfin.2.2.2.2.2⟩) (fun h => by cases h) hm
    · intro JW hJW; clear hQ hlenA hlayA hpresA hokA; c0_split
      · obtain hc2 := bv32_eq_nat 2 (by decide) hc; c0_steps
        refine hJW _ _ ⟨_, by rw [List.length_set, List.length_set, hwslA],
          fun idx hidx => by
            rw [hpos_p1, hpos_eq, List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)],
          by rw [hpos_p1, hpos_eq, List.getElem?_set_ne (by omega),
            List.getElem?_set_self (by omega)],
          fun _ => by rw [hpos_p1, List.getElem?_set_self (by rw [List.length_set]; omega)], hm⟩
      · c0_steps; have hne2 := bv32_ne_nat 2 (by decide) hc
        refine hJW _ _ ⟨_, by rw [List.length_set, hwslA],
          fun idx hidx => by rw [hpos_eq, List.getElem?_set_ne (by omega)],
          by rw [hpos_eq, List.getElem?_set_self (by omega)], fun hc2 => absurd hc2 hne2, hm⟩
  · intro JA hJA; c0_to_group
    · refine wp_join_group (fun _ mD =>
        ∃ (wvecD wstkD wsortD : List (BitVec 32)) (wlenD : Nat),
          let sD : PlainState :=
            { s with wvec := wvecD, wstk := wstkD, wlen := wlenD, wusable := 0#64,
                     heur := { s.heur with wsort := wsortD } }
          1 ≤ wlenD ∧ sD.LengthsOk c ∧ WatchStackLayout c sD ∧ WatchPresAll c s sD ∧
          (PlainMem c sD ⋆ R) mD) ?_ ?_
      · rintro _ _ mD ⟨wvecD, wstkD, wsortD, wlenD, hwd1, hlenD, hlayD, hpresD, hmD⟩
        clear hm1 hlen1 hlay1 hpres1; obtain hwleD : wlenD ≤ c.wcap := hlenD.wlen_le; c0_steps
        · exact hQ false wvecD wstkD wlenD 0#64 wsortD mD hlenD hlayD
            (fun l hl _ => hpresD l hl) (fun h => by cases h)
            (fun _ => ⟨fun hl => hpresD lit.toNat hl, Or.inr (Or.inr (Or.inr rfl))⟩) hmD
        · have hfit := bv64_fit_of_not_ugt hwleD (by omega) (x := cnt.setWidth 64) (by c0_bound)
          rw [zext_toNat _ (by decide)] at hfit
          exact hJA _ _ ⟨wvecD, wstkD, wsortD, wlenD, 0#64, hwd1, hfit, hlenD, hlayD, hpresD, hmD⟩
      · intro JD hJD; clear hQ hJA; c0_to_group
        · c0_call hDefrag; refine ⟨c, _, R, rfl, hlen1, hlay1, hm1, ?_⟩
          intro wvecD wstkD wlenD wsortD mD; dsimp only; intro hlenD hlayD h1D hpresD hmD; c0_steps
          exact hJD _ _ ⟨wvecD, wstkD, wsortD, wlenD, h1D hw1_pos, hlenD, hlayD,
            watchPresAll_trans hpres1 hpresD, hmD⟩
        · have hus0 : s.wusable = 0#64 := bv64_eq_zero_of_not_pos (by c0_bound)
          have hm1' : (PlainMem c
            { s with wvec := s.wvec, wstk := wstk1, wlen := wlen1, wusable := 0#64,
                     heur := { s.heur with wsort := s.heur.wsort } } ⋆ R) m1 := by
            rw [← hus0]; exact hm1
          exact hJD _ _ ⟨s.wvec, wstk1, s.heur.wsort, wlen1, hw1_pos,
            { hlen1 with wlen_le := hlen1.wlen_le }, hlay1.with_wstk rfl rfl rfl, hpres1, hm1'⟩
    · have hfit := bv64_fit_of_not_ugt hwle1 (by omega) (x := cnt.setWidth 64) (by c0_bound)
      rw [zext_toNat _ (by decide)] at hfit
      exact hJA _ _ ⟨s.wvec, wstk1, s.heur.wsort, wlen1, s.wusable, hw1_pos, hfit,
        hlen1, hlay1, hpres1, hm1⟩

theorem plain_watch_push_wp (Γ : Env)
    (hDefrag : ∀ a m Q X, plainWstackDefragSpec a m Q X →
      Γ "plain_wstack_defrag" [i64] [] a m Q X) :
    ∀ a m Q X, plainWatchPushSpec a m Q X → Func.wp Γ plain_watch_push_body a m Q X := by
  rintro ⟨h, lit, w0, w1, cnt, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hlay, hw0, hw1, hm, hQ⟩
  obtain hmv : c.mv < 2 ^ 28 := c.hmv; obtain hwcap : c.wcap < 2 * 2 ^ 28 := c.hwcap
  obtain hnlits : (BitVec.ofNat 64 c.mv <<< (1 : Nat)).toNat = 2 * c.mv := by
    rw [BitVec.toNat_shiftLeft, bv64_ofNat_toNat (by omega)]; simp [Nat.shiftLeft_eq]; omega
  obtain hok := hlen.heur_ok; obtain hwvl := hlen.wvec_len
  obtain hwsl := hlen.wstk_len_arr; obtain hwle := hlen.wlen_le
  c0_to_group
  · have hge : 2 * c.mv ≤ lit.toNat := by
      have : (BitVec.ofNat 64 c.mv <<< (1 : Nat)).toNat ≤ (lit.setWidth 64).toNat := by c0_bound
      rw [hnlits, zext_toNat _ (by decide)] at this; exact this
    exact hQ false s.wvec s.wstk s.wlen s.wusable s.heur.wsort m hlen hlay
      (fun _ _ _ => ⟨rfl, fun _ _ => rfl⟩) (fun h => by cases h)
      (fun _ => ⟨fun h => by omega, Or.inl (by omega)⟩) hm
  · obtain hlit_lt : lit.toNat < 2 * c.mv := by
      have : ¬ ((BitVec.ofNat 64 c.mv <<< (1 : Nat)).toNat ≤ (lit.setWidth 64).toNat) := by
        c0_bound
      rw [hnlits, zext_toNat _ (by decide)] at this; omega
    clear hc
    refine wp_join_group (fun _ m0 => (cnt.toNat = 1 ∨ cnt.toNat = 2) ∧ m = m0) ?_ ?_
    rotate_left
    · intro J0 hJ0; c0_steps
      · rename_i hc1
        exact hQ false s.wvec s.wstk s.wlen s.wusable s.heur.wsort m hlen hlay
          (fun _ _ _ => ⟨rfl, fun _ _ => rfl⟩) (fun h => by cases h)
          (fun _ => ⟨fun _ => ⟨rfl, fun _ _ => rfl⟩,
            Or.inr (Or.inl ⟨bv32_ne_nat 1 (by decide) hc1, bv32_ne_nat 2 (by decide) hc⟩)⟩) hm
      · exact hJ0 _ _ ⟨Or.inr (bv32_eq_nat 2 (by decide) hc), rfl⟩
      · exact hJ0 _ _ ⟨Or.inl (bv32_eq_nat 1 (by decide) hc), rfl⟩
    rintro _ _ m0 ⟨hcnt12, hm0⟩; rcases hm0 with rfl
    obtain hlit2 := bv64_lit2 (lit := lit); obtain hlit2p1 := bv64_lit2p1 (lit := lit)
    c0_to_group
    refine wp_join_group (fun _ m1 => ∃ (wstk1 : List (BitVec 32)) (wlen1 : Nat),
      let s1 : PlainState := { s with wstk := wstk1, wlen := wlen1 }
      1 ≤ wlen1 ∧ s1.LengthsOk c ∧ WatchStackLayout c s1 ∧ WatchPresAll c s s1 ∧
      (PlainMem c s1 ⋆ R) m1) ?_ ?_
    · rintro _ _ m1 ⟨wstk1, wlen1, hw1_pos, hlen1, hlay1, hpres1, hm1⟩; clear hm
      obtain hwsl1 : wstk1.length = c.wcap := hlen1.wstk_len_arr
      obtain hwle1 : wlen1 ≤ c.wcap := hlen1.wlen_le
      obtain hlit2_lt : (lit.setWidth 64 <<< (1 : Nat)).toNat < s.wvec.length := by omega
      obtain hlit2p1_lt : ((lit.setWidth 64 <<< (1 : Nat)) + 1).toNat < s.wvec.length := by omega
      obtain hoff1 : (s.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'hlit2_lt).toNat =
          wOff s.wvec lit.toNat := wpush_getElem_toNat hlit2_lt hlit2
      obtain hsz1 : (s.wvec[((lit.setWidth 64 <<< (1 : Nat)) + 1).toNat]'hlit2p1_lt).toNat =
          wSz s.wvec lit.toNat := wpush_getElem_toNat hlit2p1_lt hlit2p1
      obtain hoff1_le : wOff s.wvec lit.toNat + wSz s.wvec lit.toNat ≤ wlen1 :=
        hlay1.bounds lit.toNat hlit_lt
      c0_to_group
      generalize hoffV : s.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'hlit2_lt = off32 at hoff1 ⊢
      generalize hszV :
        s.wvec[((lit.setWidth 64 <<< (1 : Nat)) + 1).toNat]'hlit2p1_lt = sz32 at hsz1 ⊢
      clear hoffV hszV
      refine wp_join_group
        (fun _ mA0 => ¬ (wSz s.wvec lit.toNat = 0 ∧ wOff s.wvec lit.toNat = 0) ∧ m1 = mA0) ?_ ?_
      · rintro _ _ mA0 ⟨hnot00, hmA0⟩; rcases hmA0 with rfl
        obtain hoff1_pos : 1 ≤ wOff s.wvec lit.toNat := by
          by_cases hszp : 0 < wSz s.wvec lit.toNat
          · exact hlay1.pos_off lit.toNat hlit_lt hszp
          · omega
        obtain hend_eq : (off32.setWidth 64 + sz32.setWidth 64).toNat =
            wOff s.wvec lit.toNat + wSz s.wvec lit.toNat := by
          rw [BitVec.toNat_add, zext_toNat _ (by decide), zext_toNat _ (by decide), hoff1, hsz1]
          omega
        c0_to_group
        refine wp_join_group (fun _ mB0 => m1 = mB0) ?_ ?_
        · rintro _ _ mB0 hmB0; rcases hmB0 with rfl; c0_to_group
          refine wp_join_group (fun _ mC0 => m1 = mC0) ?_ ?_
          · rintro _ _ mC0 hmC0; rcases hmC0 with rfl; c0_to_group
            exact wpush_caseD_wp hDefrag hlit_lt hcnt12 hw0 hw1 hw1_pos hlen1 hlay1 hpres1
              hoff1 hsz1 hm1 hQ
          · intro JC hJC; clear hnlits hwsl hwle; c0_split
            · obtain hend_c_le : wOff s.wvec lit.toNat + wSz s.wvec lit.toNat + cnt.toNat ≤
                  wlen1 := by
                have h1 : (off32.setWidth 64 + sz32.setWidth 64 + cnt.setWidth 64).toNat =
                    wOff s.wvec lit.toNat + wSz s.wvec lit.toNat + cnt.toNat := by
                  rw [BitVec.toNat_add, hend_eq, zext_toNat _ (by decide)]; omega
                have h2 : (off32.setWidth 64 + sz32.setWidth 64 + cnt.setWidth 64).toNat ≤
                    (BitVec.ofNat 64 wlen1).toNat := by c0_bound
                rw [h1, bv64_ofNat_toNat (by omega)] at h2; exact h2
              clear hc; c0_to_group
              · obtain hs0 : wstk1[wOff s.wvec lit.toNat + wSz s.wvec lit.toNat]? =
                    some 0xFFFFFFFF#32 := by
                  rw [List.getElem?_eq_getElem (by omega)]; congr 1
                  have hget : wstk1[wOff s.wvec lit.toNat + wSz s.wvec lit.toNat]'(by omega) =
                      wstk1[(off32.setWidth 64 + sz32.setWidth 64).toNat]'(by omega) := by
                    congr 1; exact hend_eq.symm
                  rw [hget]; exact hc
                clear hc
                refine wp_join_group (fun _ mW => (cnt.toNat = 2 →
                  wstk1[wOff s.wvec lit.toNat + wSz s.wvec lit.toNat + 1]? = some 0xFFFFFFFF#32) ∧
                  m1 = mW) ?_ ?_
                · rintro _ _ mW ⟨hs1, hmW⟩; rcases hmW with rfl
                  obtain hdisjC := wpush_sentinel_disjoint hlay1 hlit_lt hcnt12 hs0 hs1
                  c0_to_group
                  refine wp_join_group (fun _ mW2 => ∃ wstkW : List (BitVec 32),
                    wstkW.length = c.wcap ∧
                    (∀ idx, idx ≠ wOff s.wvec lit.toNat + wSz s.wvec lit.toNat →
                      (cnt.toNat = 2 → idx ≠ wOff s.wvec lit.toNat + wSz s.wvec lit.toNat + 1) →
                      wstkW[idx]? = wstk1[idx]?) ∧
                    wstkW[wOff s.wvec lit.toNat + wSz s.wvec lit.toNat]? = some w0 ∧
                    (cnt.toNat = 2 →
                      wstkW[wOff s.wvec lit.toNat + wSz s.wvec lit.toNat + 1]? = some w1) ∧
                    (PlainMem c { s with wstk := wstkW, wlen := wlen1 } ⋆ R) mW2) ?_ ?_
                  · rintro _ _ mW2 ⟨wstkW, hwsW, hpreW, hat0W, hat1W, hmW2⟩; clear hm hJC
                    obtain hsz_new : ((sz32.setWidth 64 + cnt.setWidth 64).setWidth 32).toNat =
                        wSz s.wvec lit.toNat + cnt.toNat := by
                      have h := bv32_trunc_add (a := sz32.setWidth 64) (b := cnt)
                        (by rw [zext_toNat sz32 (by decide), hsz1]; omega)
                      rwa [zext_toNat sz32 (by decide), hsz1] at h
                    obtain hod := wvec_set_odd_u (wvec := s.wvec) (l := lit.toNat)
                      (v := (sz32.setWidth 64 + cnt.setWidth 64).setWidth 32) (by omega)
                    obtain hfin := wpush_finalize (c := c) (s := s)
                      (s2 := { s with wstk := wstk1, wlen := wlen1 }) (lit := lit.toNat)
                      (cnt := cnt.toNat) (dst := wOff s.wvec lit.toNat) (wlen' := wlen1)
                      (wvec' := s.wvec.set ((lit.setWidth 64 <<< (1 : Nat) + 1).toNat)
                        ((sz32.setWidth 64 + cnt.setWidth 64).setWidth 32))
                      (wstk' := wstkW) (wsort' := s.heur.wsort)
                      hlay1 hpres1 hlit_lt hcnt12 hw0 hw1 (Nat.le_refl _) hoff1_pos
                      (by dsimp only; omega)
                      (fun j hj hne => by
                        rw [wOff, wSz, hlit2p1, (hod j).1, (hod j).2.1 hne]; exact ⟨rfl, rfl⟩)
                      (by rw [wOff, hlit2p1, (hod lit.toNat).1])
                      (by rw [wSz, hlit2p1, (hod lit.toNat).2.2, Option.getD_some, hsz_new])
                      hdisjC
                      (fun j hj hne k hk => by
                        dsimp only at hk ⊢
                        have hd := hdisjC j hj hne (by change 0 < wSz s.wvec j; omega)
                        change wOff s.wvec j + wSz s.wvec j ≤ wOff s.wvec lit.toNat ∨
                          wOff s.wvec lit.toNat + (wSz s.wvec lit.toNat + cnt.toNat) ≤
                            wOff s.wvec j at hd
                        exact hpreW _ (by rcases hd with hd | hd <;> omega)
                          (fun _ => by rcases hd with hd | hd <;> omega))
                      (fun k hk => by
                        dsimp only at hk ⊢; exact hpreW _ (by omega) (fun _ => by omega))
                      hat0W hat1W
                    c0_steps
                    · exact hQ true _ wstkW wlen1 (s.wusable - cnt.setWidth 64) s.heur.wsort _
                        { hlen1 with wvec_len := by rw [List.length_set, hwvl],
                                     wstk_len_arr := hwsW, wlen_le := hwle1, heur_ok := hok }
                        (hfin _).1 (hfin _).2.1 (fun _ => ⟨hlit_lt, hcnt12, (hfin _).2.2.1,
                          (hfin _).2.2.2.1, (hfin _).2.2.2.2.1, (hfin _).2.2.2.2.2⟩)
                        (fun h => by cases h) hm
                    · exact hQ true _ wstkW wlen1 s.wusable s.heur.wsort _
                        { hlen1 with wvec_len := by rw [List.length_set, hwvl],
                                     wstk_len_arr := hwsW, wlen_le := hwle1, heur_ok := hok }
                        (hfin _).1 (hfin _).2.1 (fun _ => ⟨hlit_lt, hcnt12, (hfin _).2.2.1,
                          (hfin _).2.2.2.1, (hfin _).2.2.2.2.1, (hfin _).2.2.2.2.2⟩)
                        (fun h => by cases h) hm
                  · intro JW hJW; clear hQ hJC
                    obtain hend_p1 : ((off32.setWidth 64 + sz32.setWidth 64) + 1).toNat =
                        wOff s.wvec lit.toNat + wSz s.wvec lit.toNat + 1 := by
                      rw [BitVec.toNat_add, hend_eq]; simp; omega
                    c0_split
                    · obtain hc2 := bv32_eq_nat 2 (by decide) hc; c0_steps
                      refine hJW _ _ ⟨_, by rw [List.length_set, List.length_set, hwsl1],
                        fun idx hne0 hne1 => by
                          rw [hend_p1, hend_eq, List.getElem?_set_ne (by have := hne1 hc2; omega),
                            List.getElem?_set_ne (by omega)],
                        by rw [hend_p1, hend_eq, List.getElem?_set_ne (by omega),
                          List.getElem?_set_self (by omega)],
                        fun _ => by
                          rw [hend_p1, List.getElem?_set_self (by rw [List.length_set]; omega)], hm⟩
                    · c0_steps; have hne2 := bv32_ne_nat 2 (by decide) hc
                      refine hJW _ _ ⟨_, by rw [List.length_set, hwsl1],
                        fun idx hne0 _ => by rw [hend_eq, List.getElem?_set_ne (by omega)],
                        by rw [hend_eq, List.getElem?_set_self (by omega)],
                        fun hc2 => absurd hc2 hne2, hm⟩
                · intro Jc2 hJc2; c0_split
                  · c0_steps
                    exact hJc2 _ _ ⟨fun hc2 => by
                      have := bv32_eq_nat 1 (by decide) hc; omega, rfl⟩
                  · obtain hc2 : cnt.toNat = 2 := by
                      have := bv32_ne_nat 1 (by decide) hc; omega
                    clear hc
                    obtain hend_p1 : ((off32.setWidth 64 + sz32.setWidth 64) + 1).toNat =
                        wOff s.wvec lit.toNat + wSz s.wvec lit.toNat + 1 := by
                      rw [BitVec.toNat_add, hend_eq]; simp; omega
                    c0_steps
                    · exact hJc2 _ _ ⟨fun _ => by
                        rw [List.getElem?_eq_getElem (by omega)]; congr 1
                        have hidx : (off32.toNat + sz32.toNat + (1 : Val i64).toNat) % 2 ^ 64 =
                            wOff s.wvec lit.toNat + wSz s.wvec lit.toNat + 1 := by
                          rw [hoff1, hsz1]; simp; omega
                        have hget : wstk1[wOff s.wvec lit.toNat + wSz s.wvec lit.toNat + 1]'(by
                            omega) = wstk1[(off32.toNat + sz32.toNat +
                              (1 : Val i64).toNat) % 2 ^ 64]'(by rw [hidx]; omega) := by
                          congr 1; exact hidx.symm
                        rw [hget]; exact hc, rfl⟩
                    · exact hJC _ _ rfl
              · exact hJC _ _ rfl
            · c0_steps; exact hJC _ _ rfl
        · intro JB hJB; clear hnlits hwsl hwle; c0_split
          · obtain hend_wlen : wOff s.wvec lit.toNat + wSz s.wvec lit.toNat = wlen1 := by
              have := congrArg BitVec.toNat hc
              rw [hend_eq, bv64_ofNat_toNat (by omega)] at this; exact this
            clear hc; c0_split
            · obtain hfitB : cnt.toNat ≤ c.wcap - wlen1 := by
                have hsub := bv64_sub_ofNat (a := c.wcap) (b := wlen1) (by omega) (by omega)
                have : (cnt.setWidth 64).toNat ≤
                    (BitVec.ofNat 64 c.wcap - BitVec.ofNat 64 wlen1).toNat := by c0_bound
                rw [hsub, zext_toNat _ (by decide)] at this; exact this
              clear hc; c0_to_group
              refine wp_join_group (fun _ mW => ∃ wstkW : List (BitVec 32), wstkW.length = c.wcap ∧
                (∀ idx < wlen1, wstkW[idx]? = wstk1[idx]?) ∧ wstkW[wlen1]? = some w0 ∧
                (cnt.toNat = 2 → wstkW[wlen1 + 1]? = some w1) ∧
                (PlainMem c { s with wstk := wstkW, wlen := wlen1 } ⋆ R) mW) ?_ ?_
              · rintro _ _ mW ⟨wstkW, hwsW, hpreW, hat0W, hat1W, hmW⟩; clear hm hJB; c0_steps
                have hsz_new : ((sz32.setWidth 64 + cnt.setWidth 64).setWidth 32).toNat =
                    wSz s.wvec lit.toNat + cnt.toNat := by
                  have h := bv32_trunc_add (a := sz32.setWidth 64) (b := cnt)
                    (by rw [zext_toNat sz32 (by decide), hsz1]; omega)
                  rwa [zext_toNat sz32 (by decide), hsz1] at h
                have hwlen_new : ((off32.setWidth 64 + sz32.setWidth 64) +
                    cnt.setWidth 64).toNat = wlen1 + cnt.toNat := by
                  rw [BitVec.toNat_add, hend_eq, hend_wlen, zext_toNat _ (by decide)]; omega
                have hod := wvec_set_odd_u (wvec := s.wvec) (l := lit.toNat)
                  (v := (sz32.setWidth 64 + cnt.setWidth 64).setWidth 32) (by omega)
                have hfin := wpush_finalize (c := c) (s := s)
                  (s2 := { s with wstk := wstk1, wlen := wlen1 }) (lit := lit.toNat)
                  (cnt := cnt.toNat) (dst := wOff s.wvec lit.toNat)
                  (wlen' := ((off32.setWidth 64 + sz32.setWidth 64) + cnt.setWidth 64).toNat)
                  (wvec' := s.wvec.set ((lit.setWidth 64 <<< (1 : Nat) + 1).toNat)
                    ((sz32.setWidth 64 + cnt.setWidth 64).setWidth 32))
                  (wstk' := wstkW) (wsort' := s.heur.wsort) hlay1 hpres1 hlit_lt hcnt12 hw0 hw1
                  (by dsimp only; omega) hoff1_pos (by dsimp only; omega)
                  (fun j hj hne => by
                    rw [wOff, wSz, hlit2p1, (hod j).1, (hod j).2.1 hne]; exact ⟨rfl, rfl⟩)
                  (by rw [wOff, hlit2p1, (hod lit.toNat).1])
                  (by rw [wSz, hlit2p1, (hod lit.toNat).2.2, Option.getD_some, hsz_new])
                  (fun j hj hne hszj => by
                    have hbj := hlay1.bounds j hj
                    change wOff s.wvec j + wSz s.wvec j ≤ wlen1 at hbj
                    dsimp only at hszj ⊢
                    by_cases hszl : 0 < wSz s.wvec lit.toNat
                    · rcases hlay1.disjoint j lit.toNat hj hlit_lt hne hszj hszl with hd | hd
                      · exact Or.inl hd
                      · change wOff s.wvec lit.toNat + wSz s.wvec lit.toNat ≤ wOff s.wvec j at hd
                        omega
                    · exact Or.inl (by omega))
                  (fun j hj _ k hk => by
                    have hbj := hlay1.bounds j hj
                    change wOff s.wvec j + wSz s.wvec j ≤ wlen1 at hbj
                    dsimp only at hk ⊢; exact hpreW _ (by omega))
                  (fun k hk => by dsimp only at hk ⊢; exact hpreW _ (by omega))
                  (by dsimp only; rw [hend_wlen]; exact hat0W)
                  (fun hc2 => by dsimp only; rw [hend_wlen]; exact hat1W hc2) s.wusable
                exact hQ true _ wstkW _ s.wusable s.heur.wsort _
                  { hlen1 with wvec_len := by rw [List.length_set, hwvl], wstk_len_arr := hwsW,
                               wlen_le := by dsimp only; omega, heur_ok := hok }
                  hfin.1 hfin.2.1 (fun _ => ⟨hlit_lt, hcnt12, hfin.2.2.1, hfin.2.2.2.1,
                    hfin.2.2.2.2.1, hfin.2.2.2.2.2⟩) (fun h => by cases h) hm
              · intro JW hJW; clear hQ hJB
                obtain hend_p1 : ((off32.setWidth 64 + sz32.setWidth 64) + 1).toNat =
                    wlen1 + 1 := by
                  rw [BitVec.toNat_add, hend_eq, hend_wlen]; simp; omega
                c0_split
                · obtain hc2 := bv32_eq_nat 2 (by decide) hc; c0_steps
                  refine hJW _ _ ⟨_, by rw [List.length_set, List.length_set, hwsl1],
                    fun idx hidx => by
                      rw [hend_p1, hend_eq, hend_wlen, List.getElem?_set_ne (by omega),
                        List.getElem?_set_ne (by omega)],
                    by rw [hend_p1, hend_eq, hend_wlen, List.getElem?_set_ne (by omega),
                      List.getElem?_set_self (by omega)],
                    fun _ => by
                      rw [hend_p1, List.getElem?_set_self (by rw [List.length_set]; omega)], hm⟩
                · c0_steps; have hne2 := bv32_ne_nat 2 (by decide) hc
                  refine hJW _ _ ⟨_, by rw [List.length_set, hwsl1],
                    fun idx hidx => by rw [hend_eq, hend_wlen, List.getElem?_set_ne (by omega)],
                    by rw [hend_eq, hend_wlen, List.getElem?_set_self (by omega)],
                    fun hc2 => absurd hc2 hne2, hm⟩
            · c0_steps; exact hJB _ _ rfl
          · c0_steps; exact hJB _ _ rfl
      · intro JnotA hJnotA; clear hnlits hwsl hwle; c0_to_group
        · rename_i hsz_c
          obtain hsz0 : wSz s.wvec lit.toNat = 0 := by
            have := congrArg BitVec.toNat hsz_c
            rw [zext_toNat _ (by decide), hsz1] at this; exact this
          clear hJnotA hsz_c hc
          exact wpush_caseA_wp hDefrag hlit_lt hcnt12 hw0 hw1 hw1_pos hsz0 hlen1 hlay1 hpres1 hm1 hQ
        · exact hJnotA _ _ ⟨fun ⟨_, hoff0⟩ =>
            hc (BitVec.eq_of_toNat_eq (by rw [zext_toNat _ (by decide), hoff1]; exact hoff0)), rfl⟩
        · exact hJnotA _ _ ⟨fun ⟨hsz0, _⟩ =>
            hc (BitVec.eq_of_toNat_eq (by rw [zext_toNat _ (by decide), hsz1]; exact hsz0)), rfl⟩
    · intro J1 hJ1; c0_steps
      · exact hQ false s.wvec s.wstk s.wlen s.wusable s.heur.wsort m hlen hlay
          (fun _ _ _ => ⟨rfl, fun _ _ => rfl⟩) (fun h => by cases h)
          (fun _ => ⟨fun _ => ⟨rfl, fun _ _ => rfl⟩, Or.inr (Or.inr (Or.inl rfl))⟩) hm
      · rename_i hc_w0
        have hw0_eq : s.wlen = 0 := by
          have := bv64_ofNat_toNat (n := s.wlen) (by omega)
          rw [hc_w0] at this; simpa using this.symm
        have hsz_all0 : ∀ l < 2 * c.mv, watchSize s l = 0 := fun l hl => by
          have := hlay.bounds l hl; omega
        have hcap1 : 1 ≤ c.wcap := by
          have h1 : ¬ ((BitVec.ofNat 64 c.wcap).toNat < 1) := by c0_bound
          rw [bv64_ofNat_toNat (by omega)] at h1; omega
        refine hJ1 _ _ ⟨s.wstk.set 0 0#32, 1, by omega,
          { hlen with wstk_len_arr := by rw [List.length_set, hwsl],
                      wlen_le := by dsimp only; omega },
          ⟨fun l hl => by change watchOff s l + watchSize s l ≤ 1; have := hlay.bounds l hl; omega,
           fun l hl hpos => by change 0 < watchSize s l at hpos; have := hsz_all0 l hl; omega,
           fun l1 _ h1 _ _ hp1 _ => by
             change 0 < watchSize s l1 at hp1; have := hsz_all0 l1 h1; omega,
           fun l hl k hk => by change k < watchSize s l at hk; have := hsz_all0 l hl; omega⟩,
          fun l hl => ⟨rfl, fun k hk => by have := hsz_all0 l hl; omega⟩, hm⟩
      · exact hJ1 _ _ ⟨s.wstk, s.wlen, by have : s.wlen ≠ 0 := fun h0 => hc (by simp [h0]); omega,
          hlen, hlay, watchPresAll_refl c s, hm⟩

end LeanQbe.T.Examples.Kissat.Plain
