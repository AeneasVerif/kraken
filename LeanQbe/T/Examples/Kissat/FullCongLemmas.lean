module

public import LeanQbe.T.Examples.Kissat.FullCongLemmas2
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` Gate Extraction & Congruence Closure — Part 3 (`Stage 4`)

Builds on `FullCongLemmas2` to prove parametric `(Γ : Env)` `Func.wp` contracts for the final 3
congruence functions (`Full.lean` #8–10):
8. `full_cong_extract` (`full_cong_extract_wp`)
9. `full_cong_hash_step` (`full_cong_hash_step_wp`)
10. `full_congruence` (`full_congruence_wp`)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test
open FullCongSpecs FullCongHelpers
open scoped FullArenaTactics FullCongTactics

/-! ## 1. Pure Congruence-Closure & Hash-Table Lemmas -/

private theorem c0_load_full_tmp0 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) (h0 : 0 < s.core.tmp.length) :
    loadVal m i32 (c.pTmp + 0#64) = some (s.core.tmp[0]'h0) := by
  simpa using FullArenaTactics.c0_load_full_tmp (i := 0#64) (by simpa using h0) hm

private theorem c0_load_full_tmp1 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) (h1 : 1 < s.core.tmp.length) :
    loadVal m i32 (c.pTmp + 4#64) = some (s.core.tmp[1]'h1) := by
  simpa using FullArenaTactics.c0_load_full_tmp (i := 1#64) (by simpa using h1) hm

private theorem c0_load_full_tmp2 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) (h2 : 2 < s.core.tmp.length) :
    loadVal m i32 (c.pTmp + 8#64) = some (s.core.tmp[2]'h2) := by
  simpa using FullArenaTactics.c0_load_full_tmp (i := 2#64) (by simpa using h2) hm

attribute [local c0_load] c0_load_full_tmp0 c0_load_full_tmp1 c0_load_full_tmp2

private theorem congruence_gate_match {F_cur : List (List Nat)} {cur_vars g_len g ent : Nat}
    {scr0 tmp raw : List (BitVec 32)} {lhs : BitVec 32}
    (hg : GateAt F_cur cur_vars scr0 g_len g)
    (he : GateAt F_cur cur_vars scr0 g_len ent)
    (htag : ((scr0[ent + 1]?.getD 0#32) >>> 28) = ((scr0[g + 1]?.getD 0#32) >>> 28))
    (har : ((scr0[ent + 1]?.getD 0#32) &&& 0xFF#32) = ((scr0[g + 1]?.getD 0#32) &&& 0xFF#32))
    (hlhs : LitEquiv (cnfOfClauses F_cur) (scr0[g]?.getD 0#32).toNat lhs.toNat)
    (hraw_len : raw.length = ((scr0[g + 1]?.getD 0#32) &&& 0xFF#32).toNat)
    (htmp_le : raw.length ≤ tmp.length)
    (hraw_eqv : ∀ k (hk : k < raw.length),
      LitEquiv (cnfOfClauses F_cur) (scr0[g + 2 + k]?.getD 0#32).toNat (raw[k]'hk).toNat)
    (hperm : (((scr0[g + 1]?.getD 0#32) >>> 28).toNat ≠ 2 → List.Perm (tmp.take raw.length) raw) ∧
             (((scr0[g + 1]?.getD 0#32) >>> 28).toNat = 2 → tmp.take raw.length = raw))
    (hent_eqv : ∀ k (hk : k < raw.length),
      LitEquiv (cnfOfClauses F_cur) (scr0[ent + 2 + k]?.getD 0#32).toNat
        (tmp[k]'(by omega)).toNat) :
    LitEquiv (cnfOfClauses F_cur) lhs.toNat (scr0[ent]?.getD 0#32).toNat := by
  obtain ⟨lhs1, m1, hg0, hg1, _, _, _, _, hr1, hsem1⟩ := hg
  obtain ⟨lhs2, m2, he0, he1, _, _, _, _, hr2, hsem2⟩ := he
  simp only [hg0, hg1, he0, he1, Option.getD_some] at htag har hlhs hraw_len hperm ⊢
  have htag_n : (m2 >>> 28).toNat = (m1 >>> 28).toNat := congrArg BitVec.toNat htag
  have har_n : (m2 &&& 0xFF#32).toNat = (m1 &&& 0xFF#32).toNat := congrArg BitVec.toNat har
  have hscr_len_g : g + 2 + (m1 &&& 0xFF#32).toNat ≤ scr0.length := by
    rcases Nat.eq_zero_or_pos (m1 &&& 0xFF#32).toNat with hz | hpos
    · have := (List.getElem?_eq_some_iff.mp hg1).1; omega
    · obtain ⟨_, hr, _⟩ := hr1 ((m1 &&& 0xFF#32).toNat - 1) (by omega)
      have := (List.getElem?_eq_some_iff.mp hr).1; omega
  have hscr_len_e : ent + 2 + (m2 &&& 0xFF#32).toNat ≤ scr0.length := by
    rcases Nat.eq_zero_or_pos (m2 &&& 0xFF#32).toNat with hz | hpos
    · have := (List.getElem?_eq_some_iff.mp he1).1; omega
    · obtain ⟨_, hr, _⟩ := hr2 ((m2 &&& 0xFF#32).toNat - 1) (by omega)
      have := (List.getElem?_eq_some_iff.mp hr).1; omega
  rcases hsem1 with ⟨ht1, ha1, hand1⟩ | ⟨ht1, ha1, hxor1⟩ | ⟨ht1, ha1, hite1⟩ <;>
    rcases hsem2 with ⟨ht2, ha2, hand2⟩ | ⟨ht2, ha2, hxor2⟩ | ⟨ht2, ha2, hite2⟩ <;> try omega
  · have hp := hperm.1 (by omega); refine hlhs.symm.trans (congruence_andGate hand1 hand2 ?_ ?_)
    · intro x1 hx1; rw [List.mem_map] at hx1; obtain ⟨b1, hb1, rfl⟩ := hx1
      obtain ⟨j, hj, hget1⟩ := List.mem_iff_getElem.mp hb1
      rw [List.length_take, List.length_drop] at hj; have hj_ar : j < raw.length := by omega
      obtain ⟨i, hi, hti⟩ := List.mem_iff_getElem.mp (hp.symm.subset (List.getElem_mem hj_ar))
      rw [List.length_take] at hi; rw [List.getElem_take] at hti
      have hi_ar : i < raw.length := by omega
      have hb2_mem : scr0[ent + 2 + i]'(by omega) ∈
          (scr0.drop (ent + 2)).take (m2 &&& 0xFF#32).toNat := by
        have hlt : i < ((scr0.drop (ent + 2)).take (m2 &&& 0xFF#32).toNat).length := by
          rw [List.length_take, List.length_drop]; omega
        simpa [List.getElem_take, List.getElem_drop] using List.getElem_mem hlt
      refine ⟨(scr0[ent + 2 + i]'(by omega)).toNat, List.mem_map_of_mem hb2_mem, ?_⟩
      have hj_eq : (scr0[g + 2 + j]?.getD 0#32).toNat = b1.toNat := by
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
        rw [List.getElem_take, List.getElem_drop] at hget1; exact congrArg BitVec.toNat hget1
      have hi_eq : (scr0[ent + 2 + i]?.getD 0#32).toNat = (scr0[ent + 2 + i]'(by omega)).toNat :=
        by rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      have h1 := hraw_eqv j hj_ar; rw [hj_eq] at h1
      have h2 := hent_eqv i hi_ar; rw [hi_eq, hti] at h2; exact h1.trans h2.symm
    · intro x2 hx2; rw [List.mem_map] at hx2; obtain ⟨b2, hb2, rfl⟩ := hx2
      obtain ⟨i, hi, hget2⟩ := List.mem_iff_getElem.mp hb2
      rw [List.length_take, List.length_drop] at hi; have hi_ar : i < raw.length := by omega
      have htmp_mem : tmp[i]'(by omega) ∈ raw := hp.subset (by
        have hlt : i < (tmp.take raw.length).length := by rw [List.length_take]; omega
        simpa [List.getElem_take] using List.getElem_mem hlt)
      obtain ⟨j, hj, hrj⟩ := List.mem_iff_getElem.mp htmp_mem
      have hb1_mem : scr0[g + 2 + j]'(by omega) ∈
          (scr0.drop (g + 2)).take (m1 &&& 0xFF#32).toNat := by
        have hlt : j < ((scr0.drop (g + 2)).take (m1 &&& 0xFF#32).toNat).length := by
          rw [List.length_take, List.length_drop]; omega
        simpa [List.getElem_take, List.getElem_drop] using List.getElem_mem hlt
      refine ⟨(scr0[g + 2 + j]'(by omega)).toNat, List.mem_map_of_mem hb1_mem, ?_⟩
      have hj_eq : (scr0[g + 2 + j]?.getD 0#32).toNat = (scr0[g + 2 + j]'(by omega)).toNat := by
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      have hi_eq : (scr0[ent + 2 + i]?.getD 0#32).toNat = b2.toNat := by
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
        rw [List.getElem_take, List.getElem_drop] at hget2; exact congrArg BitVec.toNat hget2
      have h1 := hraw_eqv j hj; rw [hj_eq, hrj] at h1; have h2 := hent_eqv i hi_ar; rw [hi_eq] at h2
      exact h1.trans h2.symm
  · have hrl2 : raw.length = 2 := by omega
    have hp := hperm.1 (by omega); rw [hrl2, list_take2_eq (by omega)] at hp
    have hraw2 : raw = [raw[0]'(by omega), raw[1]'(by omega)] := by
      have := list_take2_eq (xs := raw) (by omega); rwa [List.take_of_length_le (by omega)] at this
    have hp2 := hp.trans (List.Perm.of_eq hraw2)
    have hg0_e := hraw_eqv 0 (by omega); have hg1_e := hraw_eqv 1 (by omega)
    have he0_e := hent_eqv 0 (by omega); have he1_e := hent_eqv 1 (by omega)
    refine hlhs.symm.trans (litEquiv_of_eval_eq fun α hα => ?_)
    rw [xorGateDef_eval hα hxor1, xorGateDef_eval hα hxor2]
    rcases perm2_cases hp2 with ⟨e0, e1⟩ | ⟨e0, e1⟩ <;>
      rw [litEquiv_eval hα hg0_e, litEquiv_eval hα hg1_e,
        litEquiv_eval hα he0_e, litEquiv_eval hα he1_e, e0, e1]
    cases evalLitVal α (raw[0]'(by omega)).toNat <;>
      cases evalLitVal α (raw[1]'(by omega)).toNat <;> rfl
  · have hrl3 : raw.length = 3 := by omega
    have hteq := hperm.2 ht1
    have hget_t : ∀ k (hk : k < 3), tmp[k]'(by omega) = raw[k]'(by omega) := fun k hk => by
      have h := congrArg (fun xs => xs[k]?) hteq
      rw [List.getElem?_take, ite_eq_left (by omega), List.getElem?_eq_getElem (by omega),
        List.getElem?_eq_getElem (by omega)] at h
      exact Option.some.inj h
    have hke : ∀ k (hk : k < 3), LitEquiv (cnfOfClauses F_cur)
        (scr0[g + 2 + k]?.getD 0#32).toNat (scr0[ent + 2 + k]?.getD 0#32).toNat := fun k hk =>
      (hraw_eqv k (by omega)).trans (by rw [← hget_t k hk]; exact (hent_eqv k (by omega)).symm)
    exact hlhs.symm.trans (congruence_iteGate hite1 hite2 (hke 0 (by omega))
      (hke 1 (by omega)) (hke 2 (by omega)))

/-! ## 2. `Func.wp` Proof #8 (`full_cong_extract`) -/

/-- **#8 (`full_cong_extract`)**: scans all arena clauses extracting AND, XOR, and ITE gates
into `scratch_buf[0 ..< ret)` while preserving `FullCoreInv` and `GateSeqOk`. -/
theorem full_cong_extract_wp (Γ : Env)
    (hNext : ∀ args m Q X, fullArenaNextSpec args m Q X →
      Γ "full_arena_next" [i64, i32] [i32] args m Q X)
    (hHasBin : ∀ args m Q X, fullHasBinSpec args m Q X →
      Γ "full_has_bin" [i64, i32, i32] [.bool] args m Q X)
    (hTryXorIte : ∀ args m Q X, fullCongTryXorIteSpec args m Q X →
      Γ "full_cong_try_xor_ite" [i64, i32, i32, i32, i64, i64] [i64] args m Q X) :
    ∀ args m Q X, fullCongExtractSpec args m Q X →
      Func.wp Γ full_cong_extract_body args m Q X := by
  rintro ⟨h, g_cap, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd, hcl0, hgc_le, hm0, hQ⟩
  have hac := c.harena; have hsc := c.hscr; have hmx := c.hmaxv
  unfold dimacsBound at hac hsc hmx; have hcl := hlen.core_ok; have hsl := hlen.scratch_ok
  have harl := hcl.arena_len_arr; have hale := hcl.arena_len_le; have hscrl := hsl.scratch_buf_len
  fc_steps; refine wp_loop_inv
    (fun (p, g_len, ()) ml => ∃ scr : List (BitVec 32),
      scr.length = c.scratch_cap ∧
      p.toNat ≤ s.core.arena_len ∧
      (p.toNat = s.core.arena_len ∨ p.toNat ∈ fullArenaClauseRefs s) ∧
      g_len.toNat ≤ g_cap.toNat ∧
      GateSeqOk F_cur s.core.cur_vars scr g_len.toNat 0 ∧
      (FullMem c { s with scratch := { s.scratch with scratch_buf := scr } } ⋆ R) ml)
    (fun (p, _, ()) _ => s.core.arena_len - p.toNat)
    (fun J hJ => by
      fc_let
      refine hJ (0#64, 0#64, ()) m0 ⟨s.scratch.scratch_buf, hscrl, Nat.zero_le _, ?_,
        Nat.zero_le _, .done, hm0⟩
      rcases Nat.eq_zero_or_pos s.core.arena_len with hz | hpos
      · exact Or.inl hz.symm
      · exact Or.inr (fullArenaClauseRefs_zero_mem hw hpos))
    (fun J (p, g_len, ()) ml ⟨scr, hscrl_c, hp_le, hp_mem, hgl_le, hseq_c, hml⟩ ih => ?_)
  let sc : FullState := { s with scratch := { s.scratch with scratch_buf := scr } }
  have hlen_c : sc.LengthsOk c :=
    ⟨hlen.core_ok, { hlen.scratch_ok with scratch_buf_len := hscrl_c }⟩
  have hq_out : Q (g_len, ()) ml := hQ g_len scr ml hscrl_c hgl_le hseq_c hml; fc_split_fast
  · have hp_lt : p.toNat < s.core.arena_len := by
      simp only [BitVec.ult, decide_eq_true_eq] at hc; bv_omega
    fc_split_fast
    · have hgl16 : g_len.toNat + 16 ≤ g_cap.toNat := by
        simp only [BitVec.ule, decide_eq_true_eq] at hc; bv_omega
      have hp_ref : p.toNat ∈ fullArenaClauseRefs s := hp_mem.resolve_left (by omega)
      have hp_wf := hw.arena.refs_wf p.toNat hp_ref
      have hp2_n : (p + 2).toNat = p.toNat + 2 :=
        show (p.toNat + 2) % 2 ^ 64 = p.toNat + 2 from Nat.mod_eq_of_lt (by omega)
      have hp_arr : p.toNat < s.core.arena.length := by omega
      have hp2_arr : (p + 2).toNat < s.core.arena.length := by omega
      fc_steps; c0_call hNext; refine ⟨c, sc, R, rfl, hlen_c, hml, ?_⟩
      have hp_tr : (p.setWidth 32).toNat = p.toNat := by
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
      have hnp_bd := fullArenaNextOff_bounds (ar := s.core.arena) (alen := s.core.arena_len)
        (cref := p.toNat) hp_wf.1
      let np_bv := (BitVec.ofNat 32 (fullArenaNextOff s.core.arena s.core.arena_len
        (p.setWidth 32).toNat)).setWidth 64
      have hnp_n : np_bv.toNat = fullArenaNextOff s.core.arena s.core.arena_len p.toNat := by
        dsimp only [np_bv]; rw [hp_tr, bv_zext32_toNat, bv32_ofNat_toNat (by omega)]
      have hnp_mem : np_bv.toNat = s.core.arena_len ∨
          np_bv.toNat ∈ fullArenaClauseRefs s := by
        rw [hnp_n]; exact fullArenaClauseRefs_next_or_end hw hp_ref
      fc_to_group; refine wp_join_group (ts := [i64])
        (fun (g_len_n, ()) mn => ∃ scr_n : List (BitVec 32),
          scr_n.length = c.scratch_cap ∧ g_len_n.toNat ≤ g_cap.toNat ∧
          GateSeqOk F_cur s.core.cur_vars scr_n g_len_n.toNat 0 ∧
          (FullMem c { s with scratch := { s.scratch with scratch_buf := scr_n } } ⋆ R) mn)
        ?_ ?_
      · rintro _ ⟨g_len_n, ⟨⟩⟩ mn ⟨scr_n, hscrl_n, hgl_n, hseq_n, hmn⟩
        fc_let; exact ih (np_bv, g_len_n, ()) mn (by dsimp only; omega)
          ⟨scr_n, hscrl_n, by omega, hnp_mem, hgl_n, hseq_n, hmn⟩
      · intro Jnp hJnp
        have hjnp0 : Jnp (g_len, ()) ml := hJnp (g_len, ()) ml ⟨scr, hscrl_c, hgl_le, hseq_c, hml⟩
        fc_split_fast
        · have hng_red := beq_iff_eq.mp hc; clear hc; fc_split_fast
          · have hsz3_bv : 3 ≤ (s.core.arena[(p + 2).toNat]'hp2_arr).toNat := by
              simp only [BitVec.ule, decide_eq_true_eq] at hc; exact hc
            clear hc; fc_split_fast
            · have hsz8_bv : (s.core.arena[(p + 2).toNat]'hp2_arr).toNat ≤ 8 := by
                simp only [BitVec.ule, decide_eq_true_eq] at hc; exact hc
              clear hc
              have hng : fullArenaClauseGarb s p.toNat = false := by
                unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
                rw [List.getElem?_eq_getElem hp_arr, Option.getD_some]
                exact garb_false_of_and_480000 hng_red
              let sz_bv := s.core.arena[(p + 2).toNat]'hp2_arr
              have hsz_bv_p2 : sz_bv = s.core.arena[p.toNat + 2]'(by omega) :=
                list_getElem_congr hp2_n hp2_arr (by omega)
              have hsz_eq : sz_bv.toNat = fullArenaClauseSizeCore s.core p.toNat := by
                unfold fullArenaClauseSizeCore
                rw [hsz_bv_p2, List.getElem?_eq_getElem (by omega), Option.getD_some]
              have hsz3 : 3 ≤ sz_bv.toNat := hsz3_bv; have hsz8 : sz_bv.toNat ≤ 8 := hsz8_bv
              have har_bd : p.toNat + 3 + sz_bv.toNat ≤ s.core.arena.length := by omega
              fc_to_group; refine wp_loop_break_group (brkTs := [i64, i32]) (lpTs := [i32])
                (fun (g_len1, _, ()) mb => ∃ scr1 : List (BitVec 32),
                  scr1.length = c.scratch_cap ∧ g_len1.toNat ≤ g_cap.toNat ∧
                  GateSeqOk F_cur s.core.cur_vars scr1 g_len1.toNat 0 ∧
                  (FullMem c { s with scratch := { s.scratch with scratch_buf := scr1 } } ⋆ R) mb)
                (fun rem (i, ()) mi =>
                  mi = ml ∧ i.toNat ≤ sz_bv.toNat ∧ rem = sz_bv.toNat - i.toNat)
                ?_ ?_ ?_
              · rintro _ ⟨g_len1, _, ⟨⟩⟩ mb ⟨scr1, hscrl1, hgl1_le, hseq1, hmb⟩
                let sc1 : FullState :=
                  { s with scratch := { s.scratch with scratch_buf := scr1 } }
                have hlen1 : sc1.LengthsOk c :=
                  ⟨hlen.core_ok, { hlen.scratch_ok with scratch_buf_len := hscrl1 }⟩
                have hjnp1 : Jnp (g_len1, ()) mb :=
                  hJnp (g_len1, ()) mb ⟨scr1, hscrl1, hgl1_le, hseq1, hmb⟩
                fc_to_group; refine wp_join_group (ts := [i64]) (fun args mj => Jnp args mj)
                  (fun _ args mj h => by fc_let; exact h) ?_
                intro J3 hJ3
                have hj3_keep : J3 (g_len1, ()) mb := hJ3 (g_len1, ()) mb hjnp1; fc_split_fast
                · have hsz_eq3 := beq_iff_eq.mp hc; clear hc; fc_split_fast
                  · have h14_le : g_len1.toNat + 14 ≤ g_cap.toNat := by
                      simp only [BitVec.ule, decide_eq_true_eq] at hc; bv_omega
                    have hsz3_n : fullArenaClauseSizeCore s.core p.toNat = 3 := by
                      rw [← hsz_eq]; exact congrArg BitVec.toNat hsz_eq3
                    have hp3_n : (p + 3).toNat = p.toNat + 3 :=
                      show (p.toNat + 3) % 2 ^ 64 = p.toNat + 3 from Nat.mod_eq_of_lt (by omega)
                    have hp4_n : (p + 4).toNat = p.toNat + 4 :=
                      show (p.toNat + 4) % 2 ^ 64 = p.toNat + 4 from Nat.mod_eq_of_lt (by omega)
                    have hp5_n : (p + 5).toNat = p.toNat + 5 :=
                      show (p.toNat + 5) % 2 ^ 64 = p.toNat + 5 from Nat.mod_eq_of_lt (by omega)
                    have hlits3 := arena_clause3_lits (k := s.core) (cr := p.toNat) hsz3_n
                      (by omega)
                    have hcl3 := hw.arena.entails p.toNat hp_ref hng
                    have hnd3 := hnd p.toNat hp_ref hng
                    have hlt3 := hw.arena.lits_lt p.toNat hp_ref hng
                    unfold fullArenaClauseLits at hnd3; rw [hlits3] at hcl3 hnd3 hlt3
                    simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
                      List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hnd3
                    have hl3 : s.core.arena[(p + 3).toNat]'(by omega) =
                        s.core.arena[p.toNat + 3]'(by omega) :=
                      list_getElem_congr hp3_n (by omega) (by omega)
                    have hl4 : s.core.arena[(p + 4).toNat]'(by omega) =
                        s.core.arena[p.toNat + 4]'(by omega) :=
                      list_getElem_congr hp4_n (by omega) (by omega)
                    have hl5 : s.core.arena[(p + 5).toNat]'(by omega) =
                        s.core.arena[p.toNat + 5]'(by omega) :=
                      list_getElem_congr hp5_n (by omega) (by omega)
                    fc_steps; c0_call hTryXorIte
                    refine ⟨c, F0, F_cur, sc1, R, rfl, hlen1, hw, hnd, hcl0,
                      by rw [hl3]; exact hlt3 _ (by simp),
                      by rw [hl4]; exact hlt3 _ (by simp),
                      by rw [hl5]; exact hlt3 _ (by simp),
                      by rw [hl3, hl4]; exact hnd3.1.1,
                      by rw [hl3, hl5]; exact hnd3.1.2,
                      by rw [hl4, hl5]; exact hnd3.2.1,
                      by rw [hl3, hl4, hl5]; exact hcl3,
                      by omega, hgc_le, hseq1, hmb,
                      fun ret scr2 m2 hlen2 _ hret_le _ hseq2 hm2 => ?_⟩
                    fc_let
                    exact hJ3 (ret, ()) m2 (hJnp (ret, ()) m2 ⟨scr2, hlen2, hret_le, hseq2, hm2⟩)
                  · fc_let; exact hj3_keep
                · fc_let; exact hj3_keep
              · rintro B L rem ⟨i, ⟨⟩⟩ mi hB hL ⟨hmi, hi_le, rfl⟩
                subst mi; fc_split_fast
                · have hi_lt : i.toNat < sz_bv.toNat := by
                    simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
                  have hp3i_n : (p + 3 + i.setWidth 64).toNat = p.toNat + 3 + i.toNat :=
                    bv64_add_zext32 (k := 3) (by omega)
                  have hp3i_arr : (p + 3 + i.setWidth 64).toNat < s.core.arena.length := by omega
                  let lhs := s.core.arena[(p + 3 + i.setWidth 64).toNat]'hp3i_arr
                  have hlhs_eq : s.core.arena[(p + 3 + i.setWidth 64).toNat]'hp3i_arr =
                      s.core.arena[p.toNat + 3 + i.toNat]?.getD 0#32 := by
                    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                    exact list_getElem_congr hp3i_n hp3i_arr (by omega)
                  fc_to_group; refine wp_loop_break_group (brkTs := [.bool, i32]) (lpTs := [i32])
                    (fun (ok, _, ()) mb2 => mb2 = ml ∧
                      (ok = true → ∀ k < sz_bv.toNat, k ≠ i.toNat →
                        (cnfOfClauses F_cur).EntailsClause (cnfClause
                          [litNeg (s.core.arena[p.toNat + 3 + i.toNat]?.getD 0#32).toNat,
                           litNeg (s.core.arena[p.toNat + 3 + k]?.getD 0#32).toNat])))
                    (fun rem2 (j, ()) mj => mj = ml ∧ j.toNat ≤ sz_bv.toNat ∧
                      rem2 = sz_bv.toNat - j.toNat ∧
                      ∀ k < j.toNat, k ≠ i.toNat →
                        (cnfOfClauses F_cur).EntailsClause (cnfClause
                          [litNeg (s.core.arena[p.toNat + 3 + i.toNat]?.getD 0#32).toNat,
                           litNeg (s.core.arena[p.toNat + 3 + k]?.getD 0#32).toNat]))
                    ?_ ?_ ?_
                  · rintro _ ⟨ok, _, ⟨⟩⟩ mb2 ⟨hmb2, hok⟩
                    subst mb2; fc_split_fast
                    · have hbins := hok hc
                      clear hc hok hL hNext hHasBin hTryXorIte hQ ih hJnp hjnp0 hq_out
                      have hi32 : i32.bytes = 4 := rfl
                      have hg1 : (g_len + 1).toNat = g_len.toNat + 1 :=
                        show (g_len.toNat + 1) % 2 ^ 64 = g_len.toNat + 1 from
                          Nat.mod_eq_of_lt (by omega)
                      have hszm1 : (sz_bv - 1#32).toNat = sz_bv.toNat - 1 := by bv_omega
                      have hgl_next : (g_len + 2#64 + (sz_bv - 1#32).setWidth 64).toNat =
                          g_len.toNat + 2 + (sz_bv.toNat - 1) := by
                        rw [bv64_add_zext32 (k := 2) (by omega), hszm1]
                      have hfs := focus_full_scratch_buf hml; clear hml
                      generalize hR_scr : FullScrBufRest c sc ⋆ R = R_scr at hfs
                      have hg0_lt : g_len.toNat < scr.length := by omega
                      have hg1_lt : (g_len + 1).toNat < scr.length := by omega
                      fc_steps; let scr_h0 := scr.set g_len.toNat lhs
                      let scr_h1 := scr_h0.set (g_len.toNat + 1) (sz_bv - 1#32)
                      have hm_h1 : (array (t := i32) c.pScratchBuf scr_h1 ⋆ R_scr) m := by
                        rw [hg1] at hm; exact hm
                      have hm_h1_full : (FullMem c { s with scratch :=
                          { s.scratch with scratch_buf := scr_h1 } } ⋆ R) m := by
                        subst hR_scr; exact unfocus_full_scratch_buf hm_h1
                      let ScrWOk (n : Nat) (scrw : List (BitVec 32)) (mj : Mem 64) : Prop :=
                        scrw.length = c.scratch_cap ∧
                        (∀ idx < g_len.toNat, scrw[idx]? = scr[idx]?) ∧
                        scrw[g_len.toNat]? = some lhs ∧
                        scrw[g_len.toNat + 1]? = some (sz_bv - 1#32) ∧
                        (∀ k < n, k ≠ i.toNat →
                          scrw[g_len.toNat + 2 + (if k < i.toNat then k else k - 1)]? =
                            some ((s.core.arena[p.toNat + 3 + k]?.getD 0#32) ^^^ 1#32)) ∧
                        (FullMem c { s with scratch := { s.scratch with scratch_buf := scrw } } ⋆ R)
                          mj
                      clear hm hm_h1; refine wp_loop_inv
                        (fun (j2, rk, ()) mj2 => ∃ scrw : List (BitVec 32),
                          j2.toNat ≤ sz_bv.toNat ∧
                          rk.toNat = (if j2.toNat ≤ i.toNat then j2.toNat else j2.toNat - 1) ∧
                          ScrWOk j2.toNat scrw mj2)
                        (fun (j2, _, ()) _ => sz_bv.toNat - j2.toNat)
                        (fun Jw hJw => by
                          fc_let; refine hJw (0#32, 0#32, ()) m
                            ⟨scr_h1, Nat.zero_le _, by simp, by simp [scr_h1, scr_h0, hscrl_c],
                             fun idx hi => by
                               simp only [scr_h1, scr_h0]
                               repeat rw [List.getElem?_set_ne (by omega)],
                             by simp only [scr_h1, scr_h0]
                                rw [List.getElem?_set_ne (by omega),
                                  List.getElem?_set_self (by omega)],
                             by simp only [scr_h1, scr_h0]
                                rw [List.getElem?_set_self (by simp [hscrl_c]; omega)],
                             fun _ hk => by simp at hk, hm_h1_full⟩)
                        (fun Jw (j2, rk, ()) mj2
                          ⟨scrw, hj2_le, hrk_eq, hscrlw, hprefw, hw0, hw1, hwrhs, hmj2⟩ ihw => ?_)
                      fc_split_fast
                      · have hj2_lt : j2.toNat < sz_bv.toNat := by
                          simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
                        have hj21 : (j2 + 1#32).toNat = j2.toNat + 1 :=
                          show (j2.toNat + 1) % 2 ^ 32 = j2.toNat + 1 from
                            Nat.mod_eq_of_lt (by omega)
                        fc_to_group; refine wp_join_group (ts := [i32])
                          (fun (rk', ()) mj2' => ∃ scrw' : List (BitVec 32),
                            rk'.toNat = (if j2.toNat + 1 ≤ i.toNat then j2.toNat + 1
                              else j2.toNat) ∧ ScrWOk (j2.toNat + 1) scrw' mj2')
                          (fun _ ⟨rk', ⟨⟩⟩ mj2' ⟨scrw', h2, h1, h3, h4, h5, h6, h7⟩ => by
                            fc_let; exact ihw (j2 + 1#32, rk', ()) mj2' (by dsimp only; omega)
                              ⟨scrw', by omega, by rw [hj21]; exact h2, h1, h3, h4, h5,
                               by rw [hj21]; exact h6, h7⟩) ?_
                        intro Jif hJif; fc_split_fast
                        · have hj2i : j2.toNat ≠ i.toNat := fun h =>
                            (bne_iff_ne.mp hc) (BitVec.eq_of_toNat_eq h)
                          have hrk_pos_eq : rk.toNat =
                              (if j2.toNat < i.toNat then j2.toNat else j2.toNat - 1) := by
                            rw [hrk_eq]; split <;> split <;> omega
                          have hrk_lt8 : rk.toNat < sz_bv.toNat - 1 := by
                            rw [hrk_pos_eq]; split <;> omega
                          have hp3j_n : (p + 3 + j2.setWidth 64).toNat = p.toNat + 3 + j2.toNat :=
                            bv64_add_zext32 (k := 3) (by omega)
                          have hp3j_arr : (p + 3 + j2.setWidth 64).toNat < s.core.arena.length := by
                            omega
                          have hdst_n : (g_len + 2 + rk.setWidth 64).toNat =
                              g_len.toNat + 2 + rk.toNat := bv64_add_zext32 (k := 2) (by omega)
                          have hdst_lt : (g_len + 2 + rk.setWidth 64).toNat < scrw.length := by
                            omega
                          have hrk1 : (rk + 1#32).toNat = rk.toNat + 1 :=
                            show (rk.toNat + 1) % 2 ^ 32 = rk.toNat + 1 from
                              Nat.mod_eq_of_lt (by omega)
                          fc_let; fc_step; have hfs_w := focus_full_scratch_buf hmj2; clear hmj2
                          generalize hR_w : FullScrBufRest c { s with scratch :=
                            { s.scratch with scratch_buf := scrw } } ⋆ R = R_w at hfs_w
                          fc_steps; subst hR_w
                          let val_j :=
                            (s.core.arena[(p + 3 + j2.setWidth 64).toNat]'hp3j_arr) ^^^ 1#32
                          have hval_j : val_j =
                              (s.core.arena[p.toNat + 3 + j2.toNat]?.getD 0#32) ^^^ 1#32 := by
                            dsimp only [val_j]; congr 1
                            rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                            exact list_getElem_congr hp3j_n hp3j_arr (by omega)
                          let scrw' := scrw.set (g_len.toNat + 2 + rk.toNat) val_j
                          have hm_w' : (FullMem c { s with scratch :=
                              { s.scratch with scratch_buf := scrw' } } ⋆ R) m := by
                            rw [hdst_n] at hm; exact unfocus_full_scratch_buf hm
                          refine hJif (rk + 1#32, ()) m
                            ⟨scrw', by rw [hrk1, hrk_eq]; split <;> split <;> omega,
                             by rw [List.length_set]; exact hscrlw,
                             fun idx hi => by
                               rw [List.getElem?_set_ne (by omega)]; exact hprefw idx hi,
                             by rw [List.getElem?_set_ne (by omega)]; exact hw0,
                             by rw [List.getElem?_set_ne (by omega)]; exact hw1,
                             fun k hk hkne => ?_, hm_w'⟩
                          by_cases hkj : k = j2.toNat
                          · subst hkj; rw [← hrk_pos_eq]
                            simp only [scrw']; rw [List.getElem?_set_self (by omega), hval_j]
                          · have hne_slot : (if k < i.toNat then k else k - 1) ≠ rk.toNat := by
                              rw [hrk_pos_eq]; split <;> split <;> omega
                            simp only [scrw']; rw [List.getElem?_set_ne (by omega)]
                            exact hwrhs k (by omega) hkne
                        · have hj2i : j2.toNat = i.toNat :=
                            congrArg BitVec.toNat (by simpa using hc : j2 = i)
                          fc_let; exact hJif (rk, ()) mj2
                            ⟨scrw, by rw [hrk_eq]; split <;> split <;> omega,
                             hscrlw, hprefw, hw0, hw1, fun k hk hkne => hwrhs k (by omega) hkne,
                             hmj2⟩
                      · have hj2_e : j2.toNat = sz_bv.toNat := by
                          simp only [BitVec.ult, decide_eq_false_iff_not] at hc
                          change ¬j2.toNat < sz_bv.toNat at hc; omega
                        rw [hj2_e] at hwrhs
                        have hsz_bv_eq : sz_bv - 1#32 = BitVec.ofNat 32 (sz_bv.toNat - 1) := by
                          apply BitVec.eq_of_toNat_eq; rw [hszm1, bv32_ofNat_toNat (by omega)]
                        have hgat := andGate_of_emitted hlen hw hnd hp_ref hng hsz_eq.symm
                          hsz3 hsz8 hi_lt hbins hscrlw (by omega) (hlhs_eq ▸ hw0)
                          (hsz_bv_eq ▸ hw1) hwrhs
                        have hseq_new : GateSeqOk F_cur s.core.cur_vars scrw
                            (g_len + 2#64 + (sz_bv - 1#32).setWidth 64).toNat 0 := by
                          rw [hgl_next]; refine gateSeqOk_append (by omega) hprefw ?_ hseq_c
                          refine .step hgat ?_
                          have hmword_ar : ((sz_bv - 1#32) &&& 0xFF#32).toNat =
                              sz_bv.toNat - 1 := by
                            rw [BitVec.toNat_and, hszm1,
                              show (0xFF#32 : BitVec 32).toNat = 255 from rfl]
                            simpa [Nat.mod_eq_of_lt (show sz_bv.toNat - 1 < 256 by omega)] using
                              Nat.and_two_pow_sub_one_eq_mod (sz_bv.toNat - 1) 8
                          simpa [hw1, hmword_ar] using GateSeqOk.done
                        fc_let; exact hB (g_len + 2#64 + (sz_bv - 1#32).setWidth 64, i, ()) mj2
                          ⟨scrw, hscrlw, by omega, hseq_new, hmj2⟩
                    · have hi1 : (i + 1#32).toNat = i.toNat + 1 :=
                        show (i.toNat + 1) % 2 ^ 32 = i.toNat + 1 from Nat.mod_eq_of_lt (by omega)
                      fc_let; exact hL (sz_bv.toNat - (i + 1#32).toNat) (i + 1#32, ()) ml (by omega)
                        ⟨rfl, by omega, rfl⟩
                  · rintro B2 L2 rem2 ⟨j, ⟨⟩⟩ mj hB2 hL2 ⟨hmj, hj_le, rfl, hseen⟩
                    subst mj; fc_split_fast
                    · have hj_lt : j.toNat < sz_bv.toNat := by
                        simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
                      have hj1 : (j + 1#32).toNat = j.toNat + 1 :=
                        show (j.toNat + 1) % 2 ^ 32 = j.toNat + 1 from Nat.mod_eq_of_lt (by omega)
                      fc_to_group; refine wp_join_group (ts := [])
                        (fun () m_j => m_j = ml ∧
                          ∀ k < (j + 1#32).toNat, k ≠ i.toNat →
                            (cnfOfClauses F_cur).EntailsClause (cnfClause
                              [litNeg (s.core.arena[p.toNat + 3 + i.toNat]?.getD 0#32).toNat,
                               litNeg (s.core.arena[p.toNat + 3 + k]?.getD 0#32).toNat]))
                        ?_ ?_
                      · rintro _ ⟨⟩ m_j ⟨hmj', hseen'⟩; subst m_j; fc_let
                        exact hL2 (sz_bv.toNat - (j + 1#32).toNat) (j + 1#32, ()) ml (by omega)
                          ⟨rfl, by omega, rfl, hseen'⟩
                      · intro Jj hJj
                        fc_let; refine ⟨fun hne => ?_, fun heq => ?_⟩
                        · have hji : j.toNat ≠ i.toNat := fun h =>
                            (bne_iff_ne.mp hne) (BitVec.eq_of_toNat_eq h)
                          have hp3j_n : (p + 3 + j.setWidth 64).toNat = p.toNat + 3 + j.toNat :=
                            bv64_add_zext32 (k := 3) (by omega)
                          have hp3j_arr : (p + 3 + j.setWidth 64).toNat < s.core.arena.length := by
                            omega
                          fc_steps; c0_call hHasBin
                          refine ⟨c, F0, F_cur, sc, R, rfl, hlen_c, hw, hml, fun hb hhb => ?_⟩
                          fc_let; refine ⟨fun hbt => ?_, fun _ => ?_⟩
                          · have hnew : (cnfOfClauses F_cur).EntailsClause (cnfClause
                                [litNeg (s.core.arena[p.toNat + 3 + i.toNat]?.getD 0#32).toNat,
                                 litNeg (s.core.arena[p.toNat + 3 + j.toNat]?.getD 0#32).toNat]) :=
                              by
                              have h := (hhb hbt).2.2.2.2
                              have hget_j : s.core.arena[(p + 3 + j.setWidth 64).toNat]'hp3j_arr =
                                  s.core.arena[p.toNat + 3 + j.toNat]?.getD 0#32 := by
                                rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                                exact list_getElem_congr hp3j_n hp3j_arr (by omega)
                              simpa only [bv32_xor1_litNeg, hlhs_eq, hget_j] using h
                            fc_let
                            exact hJj () ml ⟨rfl, fun k hk hkne => by
                              rw [hj1] at hk
                              by_cases hkj : k = j.toNat
                              · subst hkj; exact hnew
                              · exact hseen k (by omega) hkne⟩
                          · fc_let; exact hB2 (false, j, ()) ml ⟨rfl, fun h => by cases h⟩
                        · have hji : j.toNat = i.toNat := by
                            have : j = i := by simpa using heq
                            exact congrArg BitVec.toNat this
                          fc_let; exact hJj () ml ⟨rfl, fun k hk hkne => hseen k (by omega) hkne⟩
                    · have hj_e : j.toNat = sz_bv.toNat := by
                        simp only [BitVec.ult, decide_eq_false_iff_not] at hc
                        change ¬j.toNat < sz_bv.toNat at hc; omega
                      rw [hj_e] at hseen; fc_let; exact hB2 (true, j, ()) ml ⟨rfl, fun _ => hseen⟩
                  · intro _ L2 _ hL2; fc_let
                    exact hL2 (sz_bv.toNat - 0) (0#32, ()) ml
                      ⟨rfl, Nat.zero_le _, rfl, fun _ h => by simp at h⟩
                · fc_let; exact hB (g_len, i, ()) ml ⟨scr, hscrl_c, hgl_le, hseq_c, hml⟩
              · intro _ L _ hL; fc_let
                exact hL (sz_bv.toNat - 0) (0#32, ()) ml ⟨rfl, Nat.zero_le _, rfl⟩
            · fc_let; exact hjnp0
          · fc_let; exact hjnp0
        · fc_let; exact hjnp0
    · fc_let; exact hq_out
  · fc_let; exact hq_out

/-! ## 3. `Func.wp` Proof #9 (`full_cong_hash_step`) -/

/-- **#9 (`full_cong_hash_step`)**: clears the hash table `scr[ht_off ..< ht_off + ht_sz)`,
normalizes each extracted gate under `repr`, handles ITE/XOR simplifications and hash collisions
via `full_cong_merge` / `full_add_unit`, and preserves `FullDenseInv`, `CongReprInv`, and
`scr[0 ..< g_len)`. -/
theorem full_cong_hash_step_wp (Γ : Env)
    (hFind : ∀ args m Q X, fullCongFindSpec args m Q X →
      Γ "full_cong_find" [i64, i32] [i32] args m Q X)
    (hSort : ∀ args m Q X, fullSortU32Spec args m Q X →
      Γ "full_sort_u32" [i64, i32] [] args m Q X)
    (hMerge : ∀ args m Q X, fullCongMergeSpec args m Q X →
      Γ "full_cong_merge" [i64, i32, i32] [.bool] args m Q X)
    (hAddUnit : ∀ args m Q X, fullAddUnitSpec args m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] args m Q X) :
    ∀ args m Q X, fullCongHashStepSpec args m Q X →
      Func.wp Γ full_cong_hash_step_body args m Q X := by
  rintro ⟨h, g_len, ht_off, ht_sz, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hmk, hnd, hext, hcl0, hdm, hrepr0,
     hht_pos, hg_le_ht, hht_le, hseq0, hm0, hQ⟩
  have hsc := c.hscr; have hmx := c.hmaxv; unfold dimacsBound at hsc hmx
  let scr0 := s.scratch.scratch_buf; let cv0 := s.core.cur_vars
  fc_steps; have hfs0 := focus_full_scratch_buf hm0; clear hm0
  generalize hR_scr0 : FullScrBufRest c s ⋆ R = R_scr0 at hfs0
  refine wp_loop_inv
    (fun (k, ()) mk => ∃ scrk : List (BitVec 32),
      scrk.length = c.scratch_cap ∧ k.toNat ≤ ht_sz.toNat ∧
      (∀ idx < g_len.toNat, scrk[idx]? = scr0[idx]?) ∧
      (∀ j < k.toNat, scrk[ht_off.toNat + j]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) ∧
      (array (t := i32) c.pScratchBuf scrk ⋆ R_scr0) mk)
    (fun (k, ()) _ => ht_sz.toNat - k.toNat)
    (fun J hJ => by
      fc_let
      exact hJ (0#64, ()) m0 ⟨scr0, hlen.scratch_ok.scratch_buf_len, Nat.zero_le _,
        fun _ _ => rfl, fun _ h => by simp at h, hfs0⟩)
    (fun J (k, ()) mk ⟨scrk, hscrlk, hk_le, hprefk, hclrk, hmk_mem⟩ ihk => ?_)
  fc_split_fast
  · have hk_lt : k.toNat < ht_sz.toNat := by
      simp only [BitVec.ult, decide_eq_true_eq] at hc; bv_omega
    have hidx_n : (ht_off + k).toNat = ht_off.toNat + k.toNat := by bv_omega
    have hk1_n : (k + 1#64).toNat = k.toNat + 1 := by bv_omega
    have hi32 : i32.bytes = 4 := rfl; have hidx_lt : (ht_off + k).toNat < scrk.length := by omega
    fc_steps; let scrk' := scrk.set (ht_off.toNat + k.toNat) 0xFFFFFFFF#32
    have hm_set : (array (t := i32) c.pScratchBuf scrk' ⋆ R_scr0) m := by
      rw [hidx_n] at hm; exact hm
    exact ihk (k + 1#64, ()) m (by dsimp only; omega)
      ⟨scrk', by rw [List.length_set]; exact hscrlk, by omega,
       fun idx hi => by rw [List.getElem?_set_ne (by omega)]; exact hprefk idx hi,
       fun j hj => by
         by_cases hjk : j = k.toNat
         · subst hjk; rw [List.getElem?_set_self (by omega), Option.getD_some]
         · rw [List.getElem?_set_ne (by omega)]; exact hclrk j (by omega), hm_set⟩
  · have hk_eq : k.toNat = ht_sz.toNat := by
      simp only [BitVec.ult, decide_eq_false_iff_not] at hc; bv_omega
    rw [hk_eq] at hclrk; subst hR_scr0
    have hmk_mem' := unfocus_full_scratch_buf hmk_mem; clear hmk_mem
    let s0 : FullState := { s with scratch := { s.scratch with scratch_buf := scrk } }
    have hlen0 : s0.LengthsOk c :=
      ⟨hlen.core_ok, { hlen.scratch_ok with scratch_buf_len := hscrlk }⟩
    have hht0 : CongHtInv F_cur cv0 scr0 scrk g_len.toNat ht_off.toNat ht_sz.toNat :=
      fun j hj => Or.inl (hclrk j hj)
    fc_let; refine wp_loop_inv
      (fun (ch, g, ()) mg => ∃ st : FullState,
        g.toNat ≤ g_len.toNat ∧
        st.LengthsOk c ∧ FullWitnessInv c F0 F_cur st.core ∧
        FullLitMarksClear c st ∧ FullArenaVarsNodup st ∧ FullExtScratchOk c st ∧
        st.core.cur_level = 0 ∧ st.core.dense_mode ≠ 0#64 ∧
        st.core.cur_vars = cv0 ∧ st.core.fuel = s.core.fuel ∧
        st.core.arena = s.core.arena ∧ st.core.arena_len = s.core.arena_len ∧
        CongReprInv F_cur (2 * cv0) st.core.repr ∧
        (∀ idx < g_len.toNat, st.scratch.scratch_buf[idx]? = scr0[idx]?) ∧
        GateSeqOk F_cur cv0 scr0 g_len.toNat g.toNat ∧
        CongHtInv F_cur cv0 scr0 st.scratch.scratch_buf g_len.toNat ht_off.toNat ht_sz.toNat ∧
        (FullMem c st ⋆ R) mg)
      (fun (_, g, ()) _ => g_len.toNat - g.toNat)
      (fun Jg hJg => by
        fc_let
        exact hJg (false, 0#64, ()) mk ⟨s0, Nat.zero_le _, hlen0, hw, hmk, hnd, hext, hcl0, hdm,
          rfl, rfl, rfl, rfl, hrepr0, hprefk, hseq0, hht0, hmk_mem'⟩)
      (fun Jg (ch, g, ()) mg ⟨st, hg_le, hlen_t, hw_t, hmk_t, hnd_t, hext_t, hcl_t, hdm_t,
        hcv_t, hfl_t, har_t, hal_t, hrepr_t, hpref_t, hseq_t, hht_t, hmg⟩ ihg => ?_)
    have hscrl_t := hlen_t.scratch_ok.scratch_buf_len; have hcv_le := hlen_t.core_ok.cur_vars_le
    have hcv0_le : cv0 ≤ c.max_vars := hcv_t ▸ hcv_le; have htmpl_t := hlen_t.core_ok.tmp_len_arr
    have hrl_t := hlen_t.core_ok.repr_len
    have hq_done : Q (ch, ()) mg := hQ ch st mg hlen_t hw_t hmk_t hnd_t hext_t hcl_t hdm_t hcv_t
      hfl_t har_t hal_t (hcv_t ▸ hrepr_t) hpref_t hmg
    fc_split_fast
    · have hg_lt : g.toNat < g_len.toNat := by
        simp only [BitVec.ult, decide_eq_true_eq] at hc; bv_omega
      clear hc; fc_split_fast
      · clear hc; obtain ⟨hgat, hseq_next⟩ := gateSeqOk_inv_lt hseq_t hg_lt
        have ⟨lhs0, mword, hscr0_g, hscr0_g1, hlhs0_lt, hbd_g, har_cv, har_8, hrhs0, hsem0⟩ :=
          hgat
        have hg_arr : g.toNat < st.scratch.scratch_buf.length := by omega
        have hg1_n : (g + 1).toNat = g.toNat + 1 :=
          show (g.toNat + 1) % 2 ^ 64 = g.toNat + 1 from Nat.mod_eq_of_lt (by omega)
        have hg1_arr : (g + 1).toNat < st.scratch.scratch_buf.length := by omega
        have hst_g : st.scratch.scratch_buf[g.toNat]'hg_arr = lhs0 := by
          have h := (hpref_t g.toNat hg_lt).trans hscr0_g
          rw [List.getElem?_eq_getElem hg_arr] at h; exact Option.some.inj h
        have hst_g1 : st.scratch.scratch_buf[(g + 1).toNat]'hg1_arr = mword := by
          have h := (hpref_t (g.toNat + 1) (by omega)).trans hscr0_g1
          rw [← hg1_n, List.getElem?_eq_getElem hg1_arr] at h; exact Option.some.inj h
        let tag := mword >>> 28; let arity := mword &&& 0xFF#32
        have htag_def : tag.toNat = (mword >>> 28).toNat := rfl
        have har_def : arity.toNat = (mword &&& 0xFF#32).toNat := rfl
        have har_cv' : arity.toNat ≤ cv0 := har_cv
        have hbd_g' : g.toNat + 2 + arity.toNat ≤ g_len.toNat := hbd_g
        have hnext_g : (g + 2#64 + arity.setWidth 64).toNat = g.toNat + 2 + arity.toNat :=
          bv64_add_zext32 (k := 2) (by omega)
        have hseq_next' : GateSeqOk F_cur cv0 scr0 g_len.toNat
            (g + 2#64 + arity.setWidth 64).toNat := by
          rw [hnext_g]; simpa [hscr0_g1, arity] using hseq_next
        fc_steps; c0_call hFind
        refine ⟨F_cur, 2 * cv0, st.core.repr, FullReprRest c st ⋆ R, hrepr_t,
          by rw [hst_g]; exact hlhs0_lt, focus_full_repr hmg,
          fun lhs repr1 m1 hrl1 hrepr1 _ hlhs_lt hlhs_eqv hm1 => ?_⟩
        let st1 : FullState := { st with core := { st.core with repr := repr1 } }
        have hscrl1 : st1.scratch.scratch_buf.length = c.scratch_cap := hscrl_t
        have hst1_g1_c0 : st1.scratch.scratch_buf[(g + 1).toNat]'hg1_arr = mword := hst_g1
        have hlen1 : st1.LengthsOk c :=
          ⟨{ hlen_t.core_ok with repr_len := by simp [st1, hrl1, hrl_t] }, hlen_t.scratch_ok⟩
        have hw1 : FullWitnessInv c F0 F_cur st1.core := fullWitnessInv_with_repr hw_t repr1
        have hm1' : (FullMem c st1 ⋆ R) m1 := unfocus_full_repr hm1; clear hm1
        have hlhs_eqv0 : LitEquiv (cnfOfClauses F_cur) lhs0.toNat lhs.toNat := by
          rwa [hst_g] at hlhs_eqv
        fc_to_group; refine wp_loop_inv
          (fun (i, ()) mi => ∃ (repri tmpi : List (BitVec 32))
            (_ : tmpi.length = c.max_vars) (_ : i.toNat ≤ arity.toNat),
            repri.length = 2 * c.max_vars ∧
            CongReprInv F_cur (2 * cv0) repri ∧
            (∀ k' (_ : k' < i.toNat), (tmpi[k']'(by omega)).toNat < 2 * cv0 ∧
              LitEquiv (cnfOfClauses F_cur) (scr0[g.toNat + 2 + k']?.getD 0#32).toNat
                (tmpi[k']'(by omega)).toNat) ∧
            (FullMem c { st1 with core := { st1.core with repr := repri, tmp := tmpi } } ⋆ R) mi)
          (fun (i, ()) _ => arity.toNat - i.toNat)
          (fun Ji hJi => by
            fc_let
            exact hJi (0#32, ()) m1 ⟨repr1, st.core.tmp, htmpl_t, Nat.zero_le _, by omega,
              hrepr1, fun _ h => by simp at h, hm1'⟩)
          (fun Ji (i, ()) mi ⟨repri, tmpi, htl_i, hi_le, hrl_i, hrepr_i, htmp_i, hmi⟩ ihi => ?_)
        let sti : FullState := { st1 with core := { st1.core with repr := repri, tmp := tmpi } }
        fc_split_fast
        · have hi_lt : i.toNat < arity.toNat := by
            simp only [BitVec.ult, decide_eq_true_eq] at hc; rw [hst1_g1_c0] at hc; exact hc
          obtain ⟨ri, hri_get, hri_lt⟩ := hrhs0 i.toNat hi_lt
          have hg2i_n : (g + 2 + i.setWidth 64).toNat = g.toNat + 2 + i.toNat :=
            bv64_add_zext32 (k := 2) (by omega)
          have hg2i_arr : (g + 2 + i.setWidth 64).toNat < st1.scratch.scratch_buf.length := by
            omega
          have hst_g2i : st1.scratch.scratch_buf[(g + 2 + i.setWidth 64).toNat]'hg2i_arr =
              ri := by
            have h := (hpref_t (g.toNat + 2 + i.toNat) (by omega)).trans hri_get
            rw [← hg2i_n, List.getElem?_eq_getElem hg2i_arr] at h; exact Option.some.inj h
          fc_steps; c0_call hFind
          refine ⟨F_cur, 2 * cv0, repri, FullReprRest c sti ⋆ R, hrepr_i,
            by rw [hst_g2i]; exact hri_lt, focus_full_repr hmi,
            fun rval repri' mi' hrl_i' hrepr_i' _ hrval_lt hrval_eqv hmi' => ?_⟩
          let sti' : FullState := { sti with core := { sti.core with repr := repri' } }
          have hmi'' : (FullMem c sti' ⋆ R) mi' := unfocus_full_repr hmi'; clear hmi'
          have hi_tmp : i.toNat < tmpi.length := by omega
          have hi1_n : (i + 1#32).toNat = i.toNat + 1 :=
            show (i.toNat + 1) % 2 ^ 32 = i.toNat + 1 from Nat.mod_eq_of_lt (by omega)
          have hfs_tmp := focus_full_tmp hmi''; clear hmi''
          generalize hR_tmp : FullTmpRest c sti' ⋆ R = R_tmp at hfs_tmp
          have hi32 : i32.bytes = 4 := rfl; fc_steps
          subst hR_tmp; let tmpi' := tmpi.set i.toNat rval
          have hm_set : (FullMem c { st1 with core :=
              { st1.core with repr := repri', tmp := tmpi' } } ⋆ R) m := by
            rw [bv_zext32_toNat] at hm; exact unfocus_full_tmp hm
          refine ihi (i + 1#32, ()) m (by dsimp only; omega)
            ⟨repri', tmpi', by rw [List.length_set]; exact htl_i, by omega, by omega, hrepr_i',
             fun k' hk' => ?_, hm_set⟩
          rw [hi1_n] at hk'
          by_cases hki : k' = i.toNat
          · subst hki
            have hget_s : tmpi'[i.toNat]'(by simp [tmpi', htl_i]; omega) = rval := by
              simp [tmpi']
            rw [hget_s, hri_get, Option.getD_some]; exact ⟨hrval_lt, by rwa [hst_g2i] at hrval_eqv⟩
          · have hget_s : tmpi'[k']'(by simp [tmpi', htl_i]; omega) = tmpi[k']'(by omega) := by
              simp [tmpi', List.getElem_set_ne (Ne.symm hki)]
            rw [hget_s]; exact htmp_i k' (by omega)
        · have hi_eq : i.toNat = arity.toNat := by
            simp only [BitVec.ult, decide_eq_false_iff_not] at hc; rw [hst1_g1_c0] at hc
            change ¬i.toNat < arity.toNat at hc; omega
          have htmp_i : ∀ k' (_ : k' < arity.toNat), (tmpi[k']'(by omega)).toNat < 2 * cv0 ∧
              LitEquiv (cnfOfClauses F_cur) (scr0[g.toNat + 2 + k']?.getD 0#32).toNat
                (tmpi[k']'(by omega)).toNat := fun k' hk' => htmp_i k' (by omega)
          let raw := tmpi.take arity.toNat
          have hraw_len : raw.length = arity.toNat := by simp [raw]; omega
          have hraw_eqv : ∀ k' (hk' : k' < raw.length),
              LitEquiv (cnfOfClauses F_cur) (scr0[g.toNat + 2 + k']?.getD 0#32).toNat
                (raw[k']'hk').toNat := fun k' hk' => by
            have hk'' : k' < arity.toNat := by omega
            have hget : raw[k']'hk' = tmpi[k']'(by omega) := List.getElem_take
            rw [hget]; exact (htmp_i k' hk'').2
          fc_to_group; refine wp_join_group (ts := [])
            (fun () ms => ∃ tmps : List (BitVec 32),
              tmps.length = c.max_vars ∧
              (tag.toNat ≠ 2 → List.Perm (tmps.take arity.toNat) raw) ∧
              (tag.toNat = 2 → tmps.take arity.toNat = raw) ∧
              (FullMem c { st1 with core := { st1.core with repr := repri, tmp := tmps } } ⋆ R)
                ms)
            ?_ ?_
          · rintro _ ⟨⟩ ms ⟨tmps, htl_s, hperm_ne2, hperm_eq2, hms⟩
            let sts : FullState :=
              { st1 with core := { st1.core with repr := repri, tmp := tmps } }
            have hlen_s : sts.LengthsOk c :=
              ⟨{ hlen1.core_ok with repr_len := hrl_i, tmp_len_arr := htl_s }, hlen1.scratch_ok⟩
            have hw_s : FullWitnessInv c F0 F_cur sts.core :=
              fullWitnessInv_with_tmp (fullWitnessInv_with_repr hw1 repri) tmps
            fc_to_group
            refine wp_join_group (ts := []) (fun () m_after_ite => m_after_ite = ms) ?_ ?_
            · -- Not (tag == 2 && tmp[1] == tmp[2]): check XOR self-var, then hash probe
              rintro _ ⟨⟩ m_ai hmai; subst m_ai
              fc_to_group
              refine wp_join_group (ts := []) (fun () m_after_xor => m_after_xor = ms) ?_ ?_
              · -- Normal hash-table lookup / insertion path!
                rintro _ ⟨⟩ m_ax hmax; subst m_ax
                fc_let; refine wp_loop_inv
                  (fun (ih_v, _hv, ()) mhv => mhv = ms ∧ ih_v.toNat ≤ arity.toNat)
                  (fun (ih_v, _, ()) _ => arity.toNat - ih_v.toNat)
                  (fun Jhv hJhv => by
                    fc_let; exact hJhv (0#32, _, ()) ms ⟨rfl, Nat.zero_le _⟩)
                  (fun Jhv (ih_v, hv, ()) mhv ⟨hmhv, hih_le⟩ ih_hv => ?_)
                subst mhv; fc_split_fast
                · have hih_lt : ih_v.toNat < arity.toNat := by
                    simp only [BitVec.ult, decide_eq_true_eq] at hc; rw [hst1_g1_c0] at hc; exact hc
                  have hih_tmp : (ih_v.setWidth 64).toNat < tmps.length := by
                    rw [bv_zext32_toNat]; omega
                  have hih1 : (ih_v + 1#32).toNat = ih_v.toNat + 1 :=
                    show (ih_v.toNat + 1) % 2 ^ 32 = ih_v.toNat + 1 from
                      Nat.mod_eq_of_lt (by omega)
                  fc_steps
                  exact ih_hv (ih_v + 1#32, _, ()) ms (by dsimp only; omega) ⟨rfl, by omega⟩
                · let StOk (stp : FullState) (mp : Mem 64) : Prop :=
                    stp.LengthsOk c ∧ FullWitnessInv c F0 F_cur stp.core ∧
                    FullLitMarksClear c stp ∧ FullArenaVarsNodup stp ∧ FullExtScratchOk c stp ∧
                    stp.core.cur_level = 0 ∧ stp.core.dense_mode ≠ 0#64 ∧
                    stp.core.cur_vars = cv0 ∧ stp.core.fuel = s.core.fuel ∧
                    stp.core.arena = s.core.arena ∧ stp.core.arena_len = s.core.arena_len ∧
                    CongReprInv F_cur (2 * cv0) stp.core.repr ∧
                    (∀ idx < g_len.toNat, stp.scratch.scratch_buf[idx]? = scr0[idx]?) ∧
                    CongHtInv F_cur cv0 scr0 stp.scratch.scratch_buf g_len.toNat ht_off.toNat
                      ht_sz.toNat ∧ (FullMem c stp ⋆ R) mp
                  fc_to_group; refine wp_loop_break_group (brkTs := [.bool, i32, i64, i64])
                    (lpTs := [i32, i64, i64])
                    (fun (ch_p, _, _, _, ()) mp => ∃ stp : FullState, StOk stp mp)
                    (fun remp (_ip, slot, probes, ()) mp => ∃ stp : FullState,
                      slot.toNat < ht_sz.toNat ∧ probes.toNat ≤ 16 ∧ remp = 16 - probes.toNat ∧
                      stp.core.tmp = tmps ∧ StOk stp mp)
                    ?_ ?_ ?_
                  · rintro _ ⟨ch_p, _, _, _, ⟨⟩⟩ mp ⟨stp, hlen_p, hw_p, hmk_p, hnd_p, hext_p,
                      hcl_p, hdm_p, hcv_p, hfl_p, har_p, hal_p, hrepr_p, hpref_p, hht_p, hmp⟩
                    fc_let; rw [hst1_g1_c0]
                    exact ihg (ch_p, g + 2#64 + arity.setWidth 64, ()) mp
                      (by dsimp only; omega)
                      ⟨stp, by omega, hlen_p, hw_p, hmk_p, hnd_p, hext_p, hcl_p,
                       hdm_p, hcv_p, hfl_p, har_p, hal_p, hrepr_p, hpref_p,
                       hseq_next', hht_p, hmp⟩
                  · rintro Bp Lp remp ⟨ip, slot, probes, ⟨⟩⟩ mp hBp hLp
                      ⟨stp, hslot_lt, hpr_le, rfl, htmp_p, hlen_p, hw_p, hmk_p, hnd_p, hext_p,
                       hcl_p, hdm_p, hcv_p, hfl_p, har_p, hal_p, hrepr_p, hpref_p, hht_p, hmp⟩
                    have hscrl_p := hlen_p.scratch_ok.scratch_buf_len
                    have hrl_p := hlen_p.core_ok.repr_len; fc_split_fast
                    · have hpr_lt : probes.toNat < 16 := by
                        simp only [BitVec.ult, decide_eq_true_eq] at hc; bv_omega
                      have hhts_n : (ht_off + slot).toNat = ht_off.toNat + slot.toNat := by
                        bv_omega
                      have hhts_arr : (ht_off + slot).toNat < stp.scratch.scratch_buf.length := by
                        omega
                      let ent := stp.scratch.scratch_buf[(ht_off + slot).toNat]'hhts_arr
                      have hent_slot : stp.scratch.scratch_buf[ht_off.toNat + slot.toNat]?.getD
                          0xFFFFFFFF#32 = ent := by
                        rw [← hhts_n, List.getElem?_eq_getElem hhts_arr, Option.getD_some]
                      clear hc; fc_split_fast
                      · -- ent == 0xFFFFFFFF -> insert (u32)g and break!
                        have hg_tr : (g.setWidth 32).toNat = g.toNat := by
                          rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                        have hfs_p := focus_full_scratch_buf hmp; clear hmp
                        generalize hR_p : FullScrBufRest c stp ⋆ R = R_p at hfs_p
                        have hi32 : i32.bytes = 4 := rfl; fc_let; try dsimp only [lift2]
                        fc_steps; subst hR_p
                        let scr_ins := stp.scratch.scratch_buf.set (ht_off.toNat + slot.toNat)
                          (g.setWidth 32)
                        let stp' : FullState := { stp with scratch :=
                          { stp.scratch with scratch_buf := scr_ins } }
                        have hlen_p' : stp'.LengthsOk c :=
                          ⟨hlen_p.core_ok,
                           { hlen_p.scratch_ok with
                             scratch_buf_len := by rw [List.length_set]; exact hscrl_p }⟩
                        have hht_p' : CongHtInv F_cur cv0 scr0 scr_ins g_len.toNat ht_off.toNat
                            ht_sz.toNat := fun k' hk' => by
                          by_cases hks : k' = slot.toNat
                          · subst hks; right
                            rw [List.getElem?_set_self (by omega), Option.getD_some, hg_tr]
                            exact hgat
                          · rw [List.getElem?_set_ne (by omega)]; exact hht_p k' hk'
                        have hm_ins : (FullMem c stp' ⋆ R) m := by
                          rw [hhts_n] at hm; exact unfocus_full_scratch_buf hm
                        exact hBp (ch, ip, slot, probes, ()) m ⟨stp', hlen_p', hw_p, hmk_p,
                          hnd_p, hext_p, hcl_p, hdm_p, hcv_p, hfl_p, har_p, hal_p, hrepr_p,
                          fun idx hi => by
                            rw [List.getElem?_set_ne (by omega)]; exact hpref_p idx hi,
                          hht_p', hm_ins⟩
                      · -- ent != 0xFFFFFFFF -> inspect gate at ent
                        have hent_ne : ent ≠ 0xFFFFFFFF#32 := beq_eq_false_iff_ne.mp hc
                        have hent_gate : GateAt F_cur cv0 scr0 g_len.toNat ent.toNat := by
                          rcases hht_p slot.toNat hslot_lt with he | hg_e
                          · rw [hent_slot] at he; exact absurd he hent_ne
                          · rwa [hent_slot] at hg_e
                        have ⟨elhs, emword, he0, he1, helhs_lt, hbd_e, _, _, herhs, _⟩ :=
                          hent_gate
                        have he1_n : (ent.setWidth 64 + 1).toNat = ent.toNat + 1 := by
                          rw [BitVec.toNat_add, bv_zext32_toNat]
                          show (ent.toNat + 1) % 2 ^ 64 = ent.toNat + 1; omega
                        have he1_arr : (ent.setWidth 64 + 1).toNat <
                            stp.scratch.scratch_buf.length := by omega
                        have hst_e1_c0 : stp.scratch.scratch_buf[
                            (ent.setWidth 64 + 1).toNat]'he1_arr = emword := by
                          have h := (hpref_p (ent.toNat + 1) (by omega)).trans he1
                          rw [← he1_n, List.getElem?_eq_getElem he1_arr] at h
                          exact Option.some.inj h
                        have hslot_next_lt : ((slot + 1#64) &&& (ht_sz - 1#64)).toNat <
                            ht_sz.toNat := bv64_and_sub1_lt hht_pos
                        have hpr1 : (probes + 1#64).toNat = probes.toNat + 1 :=
                          show (probes.toNat + 1) % 2 ^ 64 = probes.toNat + 1 from
                            Nat.mod_eq_of_lt (by omega)
                        fc_to_group; refine wp_join_group (ts := [.bool, i32])
                          (fun (_ch_n, ip_n, ()) m_nxt => ∃ repr_n : List (BitVec 32),
                            repr_n.length = 2 * c.max_vars ∧
                            CongReprInv F_cur (2 * cv0) repr_n ∧
                            (FullMem c { stp with core := { stp.core with repr := repr_n } } ⋆ R)
                              m_nxt)
                          ?_ ?_
                        · rintro _ ⟨_ch_n, ip_n, ⟨⟩⟩ m_nxt ⟨repr_n, hrl_n, hrepr_n, hmn⟩
                          let stn : FullState :=
                            { stp with core := { stp.core with repr := repr_n } }
                          fc_let; exact hLp (16 - (probes + 1#64).toNat)
                            (ip_n, (slot + 1#64) &&& (ht_sz - 1#64), probes + 1#64, ()) m_nxt
                            (by omega)
                            ⟨stn, hslot_next_lt, by omega, rfl, htmp_p,
                             ⟨{ hlen_p.core_ok with repr_len := hrl_n }, hlen_p.scratch_ok⟩,
                             fullWitnessInv_with_repr hw_p repr_n, hmk_p, hnd_p, hext_p, hcl_p,
                             hdm_p, hcv_p, hfl_p, har_p, hal_p, hrepr_n, hpref_p, hht_p, hmn⟩
                        · intro Jnxt hJnxt
                          have hjnxt_keep : Jnxt (ch, ip, ()) mp :=
                            hJnxt (ch, ip, ()) mp ⟨stp.core.repr, hrl_p, hrepr_p, hmp⟩
                          fc_let; refine ⟨fun htag_b => ?_, fun _ => hjnxt_keep⟩
                          have htag_m := beq_iff_eq.mp htag_b
                          fc_let; refine ⟨fun har_b => ?_, fun _ => hjnxt_keep⟩
                          have har_m := beq_iff_eq.mp har_b
                          have htag_m' : (scr0[ent.toNat + 1]?.getD 0#32 >>> 28) =
                              (scr0[g.toNat + 1]?.getD 0#32 >>> 28) := by
                            rw [he1, hscr0_g1, Option.getD_some, Option.getD_some]
                            rw [hst_e1_c0, hst1_g1_c0] at htag_m; exact htag_m
                          have har_m' : (scr0[ent.toNat + 1]?.getD 0#32 &&& 0xFF#32) =
                              (scr0[g.toNat + 1]?.getD 0#32 &&& 0xFF#32) := by
                            rw [he1, hscr0_g1, Option.getD_some, Option.getD_some]
                            rw [hst_e1_c0, hst1_g1_c0] at har_m; exact har_m
                          have har_eq_e : (emword &&& 0xFF#32).toNat = arity.toNat := by
                            rw [hst_e1_c0, hst1_g1_c0] at har_m; exact congrArg BitVec.toNat har_m
                          fc_to_group
                          refine wp_loop_break_group (brkTs := [i32, i32]) (lpTs := [i32])
                            (fun (ir_b, rhs_eq, ()) mr => ∃ repr_r : List (BitVec 32),
                              repr_r.length = 2 * c.max_vars ∧
                              CongReprInv F_cur (2 * cv0) repr_r ∧
                              (rhs_eq ≠ 0#32 → ∀ k' (hk' : k' < arity.toNat),
                                LitEquiv (cnfOfClauses F_cur)
                                  (scr0[ent.toNat + 2 + k']?.getD 0#32).toNat
                                  (tmps[k']'(by omega)).toNat) ∧
                              (FullMem c { stp with core :=
                                { stp.core with repr := repr_r } } ⋆ R) mr)
                            (fun remr (ir, ()) mr => ∃ (repr_r : List (BitVec 32))
                              (_ : ir.toNat ≤ arity.toNat),
                              repr_r.length = 2 * c.max_vars ∧
                              remr = arity.toNat - ir.toNat ∧
                              CongReprInv F_cur (2 * cv0) repr_r ∧
                              (∀ k' (hk' : k' < ir.toNat),
                                LitEquiv (cnfOfClauses F_cur)
                                  (scr0[ent.toNat + 2 + k']?.getD 0#32).toNat
                                  (tmps[k']'(by omega)).toNat) ∧
                              (FullMem c { stp with core :=
                                { stp.core with repr := repr_r } } ⋆ R) mr)
                            ?_ ?_ ?_
                          · rintro _ ⟨ir_b, rhs_eq, ⟨⟩⟩ mr ⟨repr_r, hrl_r, hrepr_r, hrhs_ok, hmr⟩
                            let str : FullState :=
                              { stp with core := { stp.core with repr := repr_r } }
                            have hlen_r : str.LengthsOk c :=
                              ⟨{ hlen_p.core_ok with repr_len := hrl_r }, hlen_p.scratch_ok⟩
                            have hw_r : FullWitnessInv c F0 F_cur str.core :=
                              fullWitnessInv_with_repr hw_p repr_r
                            fc_let; refine ⟨fun hne0 => ?_, fun _ => ?_⟩
                            · have hent_eqv := hrhs_ok (bne_iff_ne.mp hne0)
                              have hmatch : LitEquiv (cnfOfClauses F_cur) lhs.toNat
                                  elhs.toNat := by
                                have hm := congruence_gate_match hgat hent_gate htag_m' har_m'
                                  (by rw [hscr0_g, Option.getD_some]; exact hlhs_eqv0)
                                  (by rw [hscr0_g1, Option.getD_some]; exact hraw_len)
                                  (by rw [hraw_len]; omega) hraw_eqv
                                  ⟨fun h => by
                                     rw [hraw_len]
                                     exact hperm_ne2 (by simpa [hscr0_g1, tag] using h),
                                   fun h => by
                                     rw [hraw_len]
                                     exact hperm_eq2 (by simpa [hscr0_g1, tag] using h)⟩
                                  (fun k' hk' => hent_eqv k' (by omega))
                                rwa [he0, Option.getD_some] at hm
                              have he0_arr : ent.toNat < stp.scratch.scratch_buf.length := by
                                omega
                              have hst_e0 : stp.scratch.scratch_buf[ent.toNat]'he0_arr =
                                  elhs := by
                                have h := (hpref_p ent.toNat (by omega)).trans he0
                                rw [List.getElem?_eq_getElem he0_arr] at h
                                exact Option.some.inj h
                              have he0_z : stp.scratch.scratch_buf[(ent.setWidth 64).toNat]'
                                  (by rw [bv_zext32_toNat]; exact he0_arr) = elhs := by
                                rw [list_getElem_congr (bv_zext32_toNat ent) _ he0_arr]
                                exact hst_e0
                              fc_to_group; refine wp_join_group (ts := [.bool])
                                (fun (ch', ()) m' => Bp (ch', ir_b, slot, probes, ()) m')
                                (fun _ ⟨ch', ⟨⟩⟩ m' h => by fc_let; exact h) ?_
                              intro Jm hJm
                              fc_steps; c0_call hMerge
                              refine ⟨c, F0, F_cur, str, R, rfl, hlen_r, hw_r, hmk_p, hnd_p,
                                hext_p, hcl_p, hdm_p, hcv_p ▸ hrepr_r, hcv_p ▸ hlhs_lt,
                                by rw [hcv_p, he0_z]; exact helhs_lt,
                                by rw [he0_z]; exact hmatch, hmr,
                                fun ch_m st_m mm hlen_m hw_m hmk_m hnd_m hext_m hcl_m hdm_m
                                  hcv_m hfl_m har_m hal_m _ hscr_m hrepr_m hmm => ?_⟩
                              have hbp_m : ∀ b : Bool, Jm (b, ()) mm := fun b =>
                                hJm (b, ()) mm (hBp (b, ir_b, slot, probes, ()) mm
                                  ⟨st_m, hlen_m, hw_m, hmk_m, hnd_m, hext_m, hcl_m, hdm_m,
                                   hcv_m.trans hcv_p, hfl_m.trans hfl_p, har_m.trans har_p,
                                   hal_m.trans hal_p, (hcv_m.trans hcv_p) ▸ hrepr_m,
                                   fun idx hi => by rw [hscr_m]; exact hpref_p idx hi,
                                   by unfold CongHtInv; rw [hscr_m]; exact hht_p, hmm⟩)
                              fc_let; exact ⟨fun _ => hbp_m true, fun _ => hbp_m ch⟩
                            · fc_let; exact hJnxt (ch, ir_b, ()) mr ⟨repr_r, hrl_r, hrepr_r, hmr⟩
                          · rintro Br Lr remr ⟨ir, ⟨⟩⟩ mr hBr hLr
                              ⟨repr_r, hir_le, hrl_r, rfl, hrepr_r, hir_eqv, hmr⟩
                            let str : FullState :=
                              { stp with core := { stp.core with repr := repr_r } }
                            fc_split_fast
                            · have hir_lt : ir.toNat < arity.toNat := by
                                simp only [BitVec.ult, decide_eq_true_eq] at hc
                                rw [hst1_g1_c0] at hc; exact hc
                              obtain ⟨erv, herv_get, herv_lt⟩ := herhs ir.toNat (by omega)
                              have he2i_n : (ent.setWidth 64 + 2 + ir.setWidth 64).toNat =
                                  ent.toNat + 2 + ir.toNat := by
                                have h := bv64_add_zext32 (p := ent.setWidth 64) (k := 2)
                                  (i := ir) (by rw [bv_zext32_toNat]; omega)
                                rwa [bv_zext32_toNat] at h
                              have he2i_arr : (ent.setWidth 64 + 2 + ir.setWidth 64).toNat <
                                  stp.scratch.scratch_buf.length := by omega
                              have hst_e2i : stp.scratch.scratch_buf[
                                  (ent.setWidth 64 + 2 + ir.setWidth 64).toNat]'he2i_arr =
                                  erv := by
                                have h :=
                                  (hpref_p (ent.toNat + 2 + ir.toNat) (by omega)).trans
                                    herv_get
                                rw [← he2i_n, List.getElem?_eq_getElem he2i_arr] at h
                                exact Option.some.inj h
                              fc_steps; c0_call hFind
                              refine ⟨F_cur, 2 * cv0, repr_r, FullReprRest c str ⋆ R, hrepr_r,
                                by rw [hst_e2i]; exact herv_lt, focus_full_repr hmr,
                                fun rval repr_r' mr' hrl_r' hrepr_r' _ _ hrval_eqv hmr' => ?_⟩
                              let str' : FullState :=
                                { stp with core := { stp.core with repr := repr_r' } }
                              have hmr'' : (FullMem c str' ⋆ R) mr' := by
                                simpa [str', str] using unfocus_full_repr hmr'
                              clear hmr'; have hir_tmp : ir.toNat < tmps.length := by omega
                              have hir_str_tmp : (ir.setWidth 64).toNat < str'.core.tmp.length :=
                                by rw [bv_zext32_toNat]; dsimp [str']; rw [htmp_p]; exact hir_tmp
                              have hir1 : (ir + 1#32).toNat = ir.toNat + 1 :=
                                show (ir.toNat + 1) % 2 ^ 32 = ir.toNat + 1 from
                                  Nat.mod_eq_of_lt (by omega)
                              clear hc; fc_split_fast
                              · fc_let
                                exact hBr (ir, 0#32, ()) mr' ⟨repr_r', by omega, hrepr_r',
                                  fun h => absurd rfl h, hmr''⟩
                              · have hrval_eq : rval = tmps[ir.toNat]'hir_tmp := by
                                  have ht_eq : str'.core.tmp[(ir.setWidth 64).toNat]'
                                      hir_str_tmp = tmps[ir.toNat]'hir_tmp := by
                                    have h := list_getElem_congr (xs := str'.core.tmp)
                                      (bv_zext32_toNat ir) hir_str_tmp
                                      (by simpa [str', htmp_p] using hir_tmp)
                                    simpa [str', htmp_p] using h
                                  have h : rval = str'.core.tmp[(ir.setWidth 64).toNat]'
                                      hir_str_tmp := by simpa using hc
                                  exact h.trans ht_eq
                                fc_let; refine hLr (arity.toNat - (ir + 1#32).toNat) (ir + 1#32, ())
                                  mr' (by omega) ⟨repr_r', by omega, by omega, rfl, hrepr_r',
                                    fun k' hk' => ?_, hmr''⟩
                                rw [hir1] at hk'
                                by_cases hki : k' = ir.toNat
                                · subst hki; rw [herv_get, Option.getD_some, ← hrval_eq]
                                  rwa [hst_e2i] at hrval_eqv
                                · exact hir_eqv k' (by omega)
                            · have hir_e : ir.toNat = arity.toNat := by
                                simp only [BitVec.ult, decide_eq_false_iff_not] at hc
                                rw [hst1_g1_c0] at hc
                                change ¬ir.toNat < arity.toNat at hc; omega
                              fc_let; exact hBr (ir, 1#32, ()) mr
                                ⟨repr_r, hrl_r, hrepr_r, fun _ k' hk' => hir_eqv k' (by omega), hmr⟩
                          · intro _ Lr _ hLr; fc_let
                            exact hLr (arity.toNat - 0) (0#32, ()) mp
                              ⟨stp.core.repr, Nat.zero_le _, hrl_p, rfl, hrepr_p,
                               fun _ h => by simp at h, hmp⟩
                    · fc_let
                      exact hBp (ch, ip, slot, probes, ()) mp ⟨stp, hlen_p, hw_p, hmk_p, hnd_p,
                        hext_p, hcl_p, hdm_p, hcv_p, hfl_p, har_p, hal_p, hrepr_p, hpref_p, hht_p,
                        hmp⟩
                  · intro _ Lp _ hLp; fc_let
                    exact hLp 16 (ih_v, _ &&& (ht_sz - 1#64), 0#64, ()) ms
                      ⟨sts, bv64_and_sub1_lt hht_pos, by decide, rfl, rfl, hlen_s, hw_s, hmk_t,
                       hnd_t, hext_t, hcl_t, hdm_t, hcv_t, hfl_t, har_t, hal_t, hrepr_i, hpref_t,
                       hht_t, hms⟩
              · intro Jx hJx
                have hjx_keep : Jx () ms := hJx () ms rfl
                fc_let; refine ⟨fun htag1_b => ?_, fun _ => hjx_keep⟩
                have htag1 := beq_iff_eq.mp htag1_b
                fc_let; refine ⟨fun har2_b => ?_, fun _ => hjx_keep⟩
                have har2 := beq_iff_eq.mp har2_b
                have htag1_n : tag.toNat = 1 := by
                  rw [hst1_g1_c0] at htag1; dsimp only [tag]; rw [htag1]; rfl
                have har2_n : arity.toNat = 2 := by
                  rw [hst1_g1_c0] at har2; change arity = 2#32 at har2; rw [har2]; rfl
                have htmps_ge2 : 2 ≤ tmps.length := by omega
                fc_split_fast
                · have hvar_eq := beq_iff_eq.mp hc; clear hc
                  have hxor0 : XorGateDef (cnfOfClauses F_cur) lhs0.toNat
                      (scr0[g.toNat + 2]?.getD 0#32).toNat
                      (scr0[g.toNat + 3]?.getD 0#32).toNat := by
                    rcases hsem0 with ⟨_, _⟩ | ⟨_, _, hxor⟩ | ⟨_, _⟩ <;> first | exact hxor | omega
                  have hp2 := hperm_ne2 (by omega); have hperm_nat : List.Perm
                      [(tmps[0]'(by omega)).toNat, (tmps[1]'(by omega)).toNat]
                      [(tmpi[0]'(by omega)).toNat, (tmpi[1]'(by omega)).toNat] := by
                    have hp' := hp2.map BitVec.toNat
                    rwa [har2_n, list_take2_eq (by omega),
                      show raw = tmpi.take 2 from by simp [raw, har2_n],
                      list_take2_eq (by omega), List.map_cons, List.map_cons, List.map_nil,
                      List.map_cons, List.map_cons, List.map_nil] at hp'
                  have hvar_n : (tmps[0]'(by omega)).toNat / 2 =
                      (tmps[1]'(by omega)).toNat / 2 := by
                    have h := congrArg BitVec.toNat hvar_eq
                    simpa [sts, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] using h
                  have hunit := xor_same_var_unit hxor0 hlhs_eqv0 hperm_nat
                    (htmp_i 0 (by omega)).2 (htmp_i 1 (by omega)).2 hvar_n
                  fc_to_group; refine wp_join_group (ts := [i32])
                    (fun (ul, ()) mu => mu = ms ∧ ul.toNat < 2 * cv0 ∧
                      (cnfOfClauses F_cur).EntailsClause (cnfClause [ul.toNat]))
                    ?_ ?_
                  · rintro _ ⟨ul, ⟨⟩⟩ mu ⟨hmu_eq, hul_lt, hul_ent⟩
                    subst mu; fc_let; c0_call hAddUnit
                    refine ⟨c, F0, F_cur, sts, R, rfl, hlen_s, hw_s, hcl_t,
                      hcv_t ▸ hul_lt, hul_ent, hms,
                      fun ok_u st_u mu hlen_u hw_u hcl_u hdm_u hcv_u hfl_u hmrk_u hlm_u
                        har_u hal_u hrep_u _ hscr_u hll_u hel_u _ hmu => ?_⟩
                    have hmk_u := fullLitMarksClear_of_eq hmk_t hmrk_u hlm_u
                    have hnd_u := fullArenaVarsNodup_of_eq hnd_t har_u hal_u
                    have hext_u := fullExtScratchOk_of_eq hext_t har_u hal_u hll_u hel_u
                    fc_let; refine ⟨fun _ => ?_, fun _ => ?_⟩
                    · fc_steps
                      let st_u' : FullState := { st_u with scratch :=
                        { st_u.scratch with cong_cnt := st_u.scratch.cong_cnt + 1#64 } }
                      have hlen_u' : st_u'.LengthsOk c := ⟨hlen_u.core_ok,
                        { hlen_u.scratch_ok with
                          walk_vals_len := hlen_u.scratch_ok.walk_vals_len }⟩
                      have hg4_eq : (g + 4#64) = g + 2#64 + arity.setWidth 64 := by
                        apply BitVec.eq_of_toNat_eq
                        rw [hnext_g, har2_n, BitVec.toNat_add]
                        show (g.toNat + 4) % 2 ^ 64 = g.toNat + 2 + 2; omega
                      exact ihg (ch, g + 4#64, ()) m (by dsimp only; rw [hg4_eq]; omega)
                        ⟨st_u', by rw [hg4_eq]; omega, hlen_u', hw_u, hmk_u, hnd_u, hext_u,
                         hcl_u, hdm_u ▸ hdm_t, hcv_u.trans hcv_t, hfl_u.trans hfl_t,
                         har_u.trans har_t, hal_u.trans hal_t,
                         by dsimp only [st_u']; rw [hrep_u]; exact hrepr_i,
                         fun idx hi => by rw [hscr_u]; exact hpref_t idx hi,
                         hg4_eq ▸ hseq_next', by unfold CongHtInv; rw [hscr_u]; exact hht_t,
                         hm⟩
                    · fc_let; exact hQ true st_u mu hlen_u hw_u hmk_u hnd_u hext_u hcl_u
                        (hdm_u ▸ hdm_t) (hcv_u.trans hcv_t) (hfl_u.trans hfl_t)
                        (har_u.trans har_t) (hal_u.trans hal_t)
                        (by rw [hcv_u, hcv_t, hrep_u]; exact hrepr_i)
                        (fun idx hi => by rw [hscr_u]; exact hpref_t idx hi) hmu
                  · intro Ju hJu; fc_split_fast
                    · fc_let; exact hJu (lhs ^^^ 1#32, ()) ms
                        ⟨rfl, by rw [bv32_xor1_eq_litNeg]; exact bv32_xor1_lt_even hlhs_lt,
                         by simpa [sts, beq_iff_eq.mp hc] using hunit⟩
                    · fc_let; exact hJu (lhs, ()) ms
                        ⟨rfl, hlhs_lt,
                         by simpa [sts, beq_eq_false_iff_ne.mp hc] using hunit⟩
                · fc_let; exact hjx_keep
            · intro Ji2 hJi2
              have hji2_keep : Ji2 () ms := hJi2 () ms rfl
              fc_let; refine ⟨fun htag2_b => ?_, fun _ => hji2_keep⟩
              have htag2 := beq_iff_eq.mp htag2_b
              have htag2_n : tag.toNat = 2 := by
                rw [hst1_g1_c0] at htag2; dsimp only [tag]; rw [htag2]; rfl
              have har3 : arity.toNat = 3 := by
                rcases hsem0 with ⟨ht, _⟩ | ⟨ht, _⟩ | ⟨_, ha3, _⟩ <;> first | exact ha3 | omega
              have htmps_ge3 : 3 ≤ tmps.length := by omega
              fc_split_fast
              · have ht12_eq : tmps[1]'(by omega) = tmps[2]'(by omega) := beq_iff_eq.mp hc
                have hite0 : IteGateDef (cnfOfClauses F_cur) lhs0.toNat
                    (scr0[g.toNat + 2]?.getD 0#32).toNat (scr0[g.toNat + 3]?.getD 0#32).toNat
                    (scr0[g.toNat + 4]?.getD 0#32).toNat := by
                  rcases hsem0 with ⟨ht, _⟩ | ⟨ht, _⟩ | ⟨_, _, hite⟩ <;> first | exact hite | omega
                have heq_raw := hperm_eq2 htag2_n
                have hget_s : ∀ k' (hk' : k' < 3), tmps[k']'(by omega) = tmpi[k']'(by omega) :=
                  fun k' hk' => by
                    have h := congrArg (fun xs => xs[k']?) heq_raw
                    simp only [raw, List.getElem?_take,
                      ite_eq_left (show k' < arity.toNat by omega),
                      List.getElem?_eq_getElem (show k' < tmps.length by omega),
                      List.getElem?_eq_getElem (show k' < tmpi.length by omega)] at h
                    exact Option.some.inj h
                have ht1_lt : (tmps[1]'(by omega)).toNat < 2 * cv0 := by
                  rw [hget_s 1 (by omega)]; exact (htmp_i 1 (by omega)).1
                have ht1_eqv : LitEquiv (cnfOfClauses F_cur)
                    (scr0[g.toNat + 3]?.getD 0#32).toNat (tmps[1]'(by omega)).toNat := by
                  rw [hget_s 1 (by omega)]; exact (htmp_i 1 (by omega)).2
                have ht2_eqv : LitEquiv (cnfOfClauses F_cur)
                    (scr0[g.toNat + 4]?.getD 0#32).toNat (tmps[1]'(by omega)).toNat := by
                  rw [ht12_eq, hget_s 2 (by omega)]; exact (htmp_i 2 (by omega)).2
                have hmerg_eqv : LitEquiv (cnfOfClauses F_cur) lhs.toNat
                    (tmps[1]'(by omega)).toNat :=
                  ite_equal_branches_equiv hite0 hlhs_eqv0 ht1_eqv ht2_eqv
                fc_to_group; refine wp_join_group (ts := [.bool])
                  (fun (ch', ()) m' => Jg (ch', g + 2#64 + arity.setWidth 64, ()) m')
                  (fun _ ⟨ch', ⟨⟩⟩ m' h => by fc_let; rw [hst1_g1_c0]; exact h) ?_
                intro Jmi hJmi
                fc_steps; c0_call hMerge
                refine ⟨c, F0, F_cur, sts, R, rfl, hlen_s, hw_s, hmk_t, hnd_t, hext_t, hcl_t,
                  hdm_t, hcv_t ▸ hrepr_i, hcv_t ▸ hlhs_lt, hcv_t ▸ ht1_lt, hmerg_eqv, hms,
                  fun ch_m st_m mm hlen_m hw_m hmk_m hnd_m hext_m hcl_m hdm_m hcv_m hfl_m
                    har_m hal_m _ hscr_m hrepr_m hmm => ?_⟩
                have hih_m : ∀ b : Bool, Jmi (b, ()) mm := fun b =>
                  hJmi (b, ()) mm (ihg (b, g + 2#64 + arity.setWidth 64, ()) mm
                    (by dsimp only; omega)
                    ⟨st_m, by omega, hlen_m, hw_m, hmk_m, hnd_m, hext_m, hcl_m, hdm_m,
                     hcv_m.trans hcv_t, hfl_m.trans hfl_t, har_m.trans har_t, hal_m.trans hal_t,
                     (hcv_m.trans hcv_t) ▸ hrepr_m,
                     fun idx hi => by rw [hscr_m]; exact hpref_t idx hi,
                     hseq_next', by unfold CongHtInv; rw [hscr_m]; exact hht_t, hmm⟩)
                fc_let; exact ⟨fun _ => hih_m true, fun _ => hih_m ch⟩
              · fc_let; exact hji2_keep
          · intro Js hJs
            fc_let; refine ⟨fun hne2_b => ?_, fun heq2_b => ?_⟩
            · have hne2 : tag.toNat ≠ 2 := by
                have h := bne_iff_ne.mp hne2_b
                rw [hst1_g1_c0] at h; intro he; exact h (BitVec.eq_of_toNat_eq he)
              fc_let; c0_call hSort
              refine ⟨tmpi, FullTmpRest c sti ⋆ R,
                by rw [hst1_g1_c0]; change arity.toNat ≤ tmpi.length; omega, focus_full_tmp hmi,
                fun tmps ms htl_s hperm_s _ hms => ?_⟩
              have hms' : (FullMem c { st1 with core :=
                  { st1.core with repr := repri, tmp := tmps } } ⋆ R) ms := by
                simpa [sti] using unfocus_full_tmp hms
              clear hms; fc_let
              exact hJs () ms ⟨tmps, by omega,
                fun _ => by rw [hst1_g1_c0] at hperm_s; exact hperm_s,
                fun h => absurd h hne2, hms'⟩
            · have heq2 : tag.toNat = 2 := by
                have h : st1.scratch.scratch_buf[(g + 1).toNat]'hg1_arr >>> 28 = 2#32 := by
                  simpa using heq2_b
                rw [hst1_g1_c0] at h; dsimp only [tag]; rw [h]; rfl
              fc_let; exact hJs () mi ⟨tmpi, htl_i, fun h => absurd heq2 h, fun _ => rfl, hmi⟩
      · fc_let; exact hq_done
    · fc_let; exact hq_done

/-! ## 4. `Func.wp` Proof #10 (`full_congruence`) -/

/-- **#10 (`full_congruence`)**: top-level gate congruence closure pass switching cleanly
`FullSparseInv → FullDenseInv → FullSparseInv` (or proving `F0.Unsat` on `20#64`), preserving
fuel monotonicity (`s'.core.fuel.toNat ≤ s.core.fuel.toNat`). -/
theorem full_congruence_wp (Γ : Env)
    (hBacktrack : ∀ args m Q X, fullBacktrackSpec args m Q X →
      Γ "full_backtrack" [i64, i64] [] args m Q X)
    (hEnterDense : ∀ args m Q X, fullEnterDenseSpec args m Q X →
      Γ "full_enter_dense" [i64] [.bool] args m Q X)
    (hExtract : ∀ args m Q X, fullCongExtractSpec args m Q X →
      Γ "full_cong_extract" [i64, i64] [i64] args m Q X)
    (hHashStep : ∀ args m Q X, fullCongHashStepSpec args m Q X →
      Γ "full_cong_hash_step" [i64, i64, i64, i64] [.bool] args m Q X)
    (hRebuild : ∀ args m Q X, fullRebuildWatchesSpec args m Q X →
      Γ "full_rebuild_watches" [i64] [i64] args m Q X)
    (hProp : ∀ args m Q X, fullPropagateSpec args m Q X →
      Γ "full_propagate" [i64] [i64] args m Q X) :
    ∀ args m Q X, fullCongruenceSpec args m Q X → Func.wp Γ full_congruence_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m0 Q X ⟨c, F0, s, R, rfl, hsp0, hm0, hQ⟩
  have hsc := c.hscr; have hmx := c.hmaxv; unfold dimacsBound at hsc hmx; fc_to_group
  refine wp_join_group (ts := [])
    (fun () m1 => ∃ s1 : FullState, FullSparseInv c F0 s1 ∧ s1.core.cur_level = 0 ∧
      s1.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s1 ⋆ R) m1)
    ?_ ?_
  · rintro _ ⟨⟩ m1 ⟨s1, hsp1, hcl1, hfl1, hm1⟩
    fc_split
    · fc_steps; exact hQ 1#64 s1 m1 hfl1 (Or.inl rfl) (fun _ => hsp1) (by simp) hm1
    · have h256 : 256 ≤ c.scratch_cap := by bv_omega
      fc_steps; c0_call hEnterDense
      refine ⟨c, F0, s1, R, rfl, hsp1, hm1, fun ok_d s2 m2 hfl2 hdense hsparse hm2 => ?_⟩
      fc_split
      · have hd2 : FullDenseInv c F0 s2 := hdense (by cases ok_d <;> simp_all)
        obtain ⟨hcore2, hmk2, hnd2, hext2, hcl2, hdm2⟩ := hd2; obtain ⟨F_cur, hw2⟩ := hcore2.witness
        have hlen2 := hcore2.lengths; have hcv_le := hlen2.core_ok.cur_vars_le
        have hrl2 := hlen2.core_ok.repr_len; fc_steps
        refine wp_loop_inv
          (fun (ht_sz, ()) mht => mht = m2 ∧
            64 ≤ ht_sz.toNat ∧ ht_sz.toNat ≤ 8192 ∧ ht_sz.toNat ≤ c.scratch_cap)
          (fun (ht_sz, ()) _ => 8192 - ht_sz.toNat)
          (fun Jht hJht => by
            fc_steps
            exact hJht (64#64, ()) m2 ⟨rfl, by decide, by decide, show 64 ≤ c.scratch_cap by omega⟩)
          (fun Jht (ht_sz, ()) mht ⟨hmht, hht64, hht_le8, hht_sc⟩ ih_ht => ?_)
        subst mht; fc_to_group; refine wp_join_group (ts := []) (fun () me => me = m2) ?_ ?_
        · -- Post-ht_sz-loop body (written ONCE!)
          rintro _ ⟨⟩ me hme; subst me
          have hht_off : (BitVec.ofNat 64 c.scratch_cap - ht_sz).toNat =
              c.scratch_cap - ht_sz.toNat := by bv_omega
          fc_steps; c0_call hExtract
          refine ⟨c, F0, F_cur, s2, R, rfl, hlen2, hw2, hnd2, hcl2, by omega, hm2,
            fun g_len scr3 m3 hscrl3 hgl_le hseq3 hm3 => ?_⟩
          let s3 : FullState := { s2 with scratch := { s2.scratch with scratch_buf := scr3 } }
          have hlen3 : s3.LengthsOk c :=
            ⟨hlen2.core_ok, { hlen2.scratch_ok with scratch_buf_len := hscrl3 }⟩
          have hnlits : (BitVec.ofNat 64 s2.core.cur_vars <<< (1 : Nat)).toNat =
              2 * s2.core.cur_vars := by
            rw [bv64_shl1_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
          fc_steps; refine wp_loop_inv
            (fun (i, ()) mi => ∃ repri : List (BitVec 32),
              repri.length = 2 * c.max_vars ∧ i.toNat ≤ 2 * s2.core.cur_vars ∧
              (∀ k < i.toNat, repri[k]? = some (BitVec.ofNat 32 k)) ∧
              (FullMem c { s3 with core := { s3.core with repr := repri } } ⋆ R) mi)
            (fun (i, ()) _ => 2 * s2.core.cur_vars - i.toNat)
            (fun Ji hJi => by
              fc_steps
              exact hJi (0#64, ()) m3 ⟨s2.core.repr, hrl2, Nat.zero_le _,
                fun _ h => by simp at h, hm3⟩)
            (fun Ji (i, ()) mi ⟨repri, hrli, hi_le, hinit, hmi⟩ ihi => ?_)
          fc_split
          · have hi_lt : i.toNat < 2 * s2.core.cur_vars := by bv_omega
            have hi1_n : (i + 1#64).toNat = i.toNat + 1 :=
              show (i.toNat + 1) % 2 ^ 64 = i.toNat + 1 from Nat.mod_eq_of_lt (by omega)
            have hi_tr : i.setWidth 32 = BitVec.ofNat 32 i.toNat := by
              apply BitVec.eq_of_toNat_eq
              rw [BitVec.toNat_setWidth, bv32_ofNat_toNat (by omega), Nat.mod_eq_of_lt (by omega)]
            fc_steps; let repri' := repri.set i.toNat (i.setWidth 32)
            exact ihi (i + 1#64, ()) m (by dsimp only; omega)
              ⟨repri', by simp [repri', hrli], by omega, fun k hk => by
                rw [hi1_n] at hk
                by_cases hki : k = i.toNat
                · subst hki; rw [List.getElem?_set_self (by omega), hi_tr]
                · rw [List.getElem?_set_ne (Ne.symm hki)]; exact hinit k (by omega),
               hm⟩
          · have hi_eq : i.toNat = 2 * s2.core.cur_vars := by bv_omega
            rw [hi_eq] at hinit
            have hrepr4 : CongReprInv F_cur (2 * s2.core.cur_vars) repri := by
              refine ⟨⟨by omega, fun l hl => ?_⟩, fun l hl => ?_⟩
              · rw [hinit l hl, Option.getD_some, bv32_ofNat_toNat (by omega)]; exact Nat.le_refl _
              · rw [hinit l hl, Option.getD_some, bv32_ofNat_toNat (by omega)]
                exact LitEquiv.refl _ _
            let s4 : FullState := { s3 with core := { s3.core with repr := repri } }
            have hlen4 : s4.LengthsOk c :=
              ⟨{ hlen3.core_ok with repr_len := hrli }, hlen3.scratch_ok⟩
            have hw4 : FullWitnessInv c F0 F_cur s4.core := fullWitnessInv_with_repr hw2 repri
            fc_to_group; refine wp_loop_break_group (brkTs := [i64]) (lpTs := [i64])
              (fun (_, ()) mb => ∃ sf : FullState, FullDenseInv c F0 sf ∧
                sf.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c sf ⋆ R) mb)
              (fun remp (pass, ()) mp => ∃ sp : FullState,
                pass.toNat ≤ 6 ∧ remp = 6 - pass.toNat ∧
                sp.LengthsOk c ∧ FullWitnessInv c F0 F_cur sp.core ∧
                FullLitMarksClear c sp ∧ FullArenaVarsNodup sp ∧ FullExtScratchOk c sp ∧
                sp.core.cur_level = 0 ∧ sp.core.dense_mode ≠ 0#64 ∧
                sp.core.cur_vars = s2.core.cur_vars ∧
                sp.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                CongReprInv F_cur (2 * sp.core.cur_vars) sp.core.repr ∧
                GateSeqOk F_cur sp.core.cur_vars sp.scratch.scratch_buf g_len.toNat 0 ∧
                (FullMem c sp ⋆ R) mp)
              ?_ ?_ ?_
            · rintro _ ⟨_, ⟨⟩⟩ mb ⟨sf, hdf, hflf, hmb⟩
              fc_steps; c0_call hRebuild
              refine ⟨c, F0, sf, R, rfl, hdf, hmb,
                fun rr s6 m6 hlen6 hfl6 hrr20 hrr_ok hm6 => ?_⟩
              fc_split
              · fc_steps; exact hQ 20#64 s6 m6 (Nat.le_trans hfl6 hflf) (Or.inr rfl) (by simp)
                  (fun _ => ⟨hrr20 (by grind), hlen6⟩) hm6
              · have hrr_ne : rr ≠ 20#64 := by grind
                obtain ⟨hsp6, hcl6⟩ := hrr_ok hrr_ne; fc_split
                · fc_steps; exact hQ 20#64 s6 m6 (Nat.le_trans hfl6 hflf) (Or.inr rfl) (by simp)
                    (fun _ => ⟨hsp6.1.inconsistent_unsat (by grind), hlen6⟩) hm6
                · fc_steps; c0_call hProp
                  refine ⟨c, F0, s6, R, rfl, hsp6, hcl6, hm6,
                    fun pr s7 m7 hsp7 _ hfl7 hpr1 hm7 => ?_⟩
                  fc_split
                  · fc_steps; exact hQ 20#64 s7 m7 (Nat.le_trans hfl7 (Nat.le_trans hfl6 hflf))
                      (Or.inr rfl) (by simp) (fun _ => ⟨hpr1 (by grind), hsp7.1.lengths⟩) hm7
                  · fc_steps; exact hQ 1#64 s7 m7 (Nat.le_trans hfl7 (Nat.le_trans hfl6 hflf))
                      (Or.inl rfl) (fun _ => hsp7) (by simp) hm7
            · rintro Bp Lp remp ⟨pass, ⟨⟩⟩ mp hBp hLp
                ⟨sp, hpass_le, rfl, hlen_p, hw_p, hmk_p, hnd_p, hext_p, hcl_p, hdm_p,
                 hcv_p, hfl_p, hrepr_p, hseq_p, hmp⟩
              fc_split
              · have hpass_lt : pass.toNat < 6 := by bv_omega
                fc_split
                · have hpass1 : (pass + 1#64).toNat = pass.toNat + 1 :=
                    show (pass.toNat + 1) % 2 ^ 64 = pass.toNat + 1 from
                      Nat.mod_eq_of_lt (by omega)
                  fc_steps; c0_call hHashStep
                  refine ⟨c, F0, F_cur, sp, R, rfl, hlen_p, hw_p, hmk_p, hnd_p, hext_p, hcl_p,
                    hdm_p, hrepr_p, by omega, by omega, by omega, hseq_p, hmp,
                    fun ch sp' mp' hlen_p' hw_p' hmk_p' hnd_p' hext_p' hcl_p' hdm_p' hcv_p' hfl_p'
                      _ _ hrepr_p' hpref_p' hmp' => ?_⟩
                  fc_split
                  · fc_steps; exact hLp (6 - (pass + 1#64).toNat) (pass + 1#64, ()) mp' (by omega)
                      ⟨sp', by omega, rfl, hlen_p', hw_p', hmk_p', hnd_p', hext_p', hcl_p', hdm_p',
                       hcv_p'.trans hcv_p, by rw [hfl_p']; exact hfl_p, hrepr_p',
                       hcv_p' ▸ gateSeqOk_congr hpref_p' hseq_p, hmp'⟩
                  · fc_steps
                    exact hBp (pass, ()) mp' ⟨sp', ⟨⟨hlen_p', ⟨F_cur, hw_p'⟩⟩, hmk_p', hnd_p',
                      hext_p', hcl_p', hdm_p'⟩, by rw [hfl_p']; exact hfl_p, hmp'⟩
                · fc_steps
                  exact hBp (pass, ()) mp ⟨sp, ⟨⟨hlen_p, ⟨F_cur, hw_p⟩⟩, hmk_p, hnd_p, hext_p,
                    hcl_p, hdm_p⟩, hfl_p, hmp⟩
              · fc_steps
                exact hBp (pass, ()) mp ⟨sp, ⟨⟨hlen_p, ⟨F_cur, hw_p⟩⟩, hmk_p, hnd_p, hext_p,
                  hcl_p, hdm_p⟩, hfl_p, hmp⟩
            · intro _ Lp _ hLp; fc_steps
              exact hLp 6 (0#64, ()) mi ⟨s4, Nat.zero_le _, rfl, hlen4, hw4, hmk2, hnd2, hext2,
                hcl2, hdm2, rfl, Nat.le_trans hfl2 hfl1, hrepr4, hseq3, hmi⟩
        · intro Jht_exit hJht_exit
          fc_split
          · have h4_n : ht_sz.toNat * 4 < c.scratch_cap := by bv_omega
            fc_split
            · have h4096_n : ht_sz.toNat < 4096 := by bv_omega
              have hshl1 : (ht_sz <<< (1 : Nat)).toNat = 2 * ht_sz.toNat := by
                rw [bv64_shl1_toNat]; omega
              fc_steps; exact ih_ht (ht_sz <<< (1 : Nat), ()) m2 (by dsimp only; omega)
                ⟨rfl, by omega, by omega, by omega⟩
            · fc_steps; exact hJht_exit () m2 rfl
          · fc_steps; exact hJht_exit () m2 rfl
      · fc_steps; exact hQ 1#64 s2 m2 (Nat.le_trans hfl2 hfl1) (Or.inl rfl)
          (fun _ => hsparse (by cases ok_d <;> simp_all)) (by simp) hm2
  · intro Jb hJb; fc_split
    · fc_steps; c0_call hBacktrack
      refine ⟨c, F0, s, R, rfl, hsp0, Nat.zero_le _, hm0, fun s1 m1 hsp1 hcl1 hfl1 hm1 => ?_⟩
      fc_steps; exact hJb () m1 ⟨s1, hsp1, hcl1, hfl1, hm1⟩
    · have hcl0_s : s.core.cur_level = 0 := by
        have hlt : s.core.cur_level < 2 ^ 64 := by
          obtain ⟨_, hw0⟩ := hsp0.1.witness
          have := hw0.cur_level_le; have := hsp0.1.lengths.core_ok.trail_end_le
          have := hsp0.1.lengths.core_ok.cur_vars_le; omega
        have h := congrArg BitVec.toNat (show BitVec.ofNat 64 s.core.cur_level = 0#64 by grind)
        rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at h
      fc_steps; exact hJb () m0 ⟨s, hsp0, hcl0_s, Nat.le_refl _, hm0⟩

end LeanQbe.T.Examples.Kissat.Full
