module

public import LeanQbe.T.Examples.Kissat.FullBinLuckyLemmas1
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` Binary Watch / Unit Helpers (`Stage 4`, Part 2)

Parametric `(Γ : Env)` `Func.wp` proofs for:
- `full_add_bin`
- `full_delete_bin_side`
- `full_delete_binary`
- `full_set_inactive`
- `full_add_unit`
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
open FullBinLuckySpecs
open scoped FullArenaTactics FullBinLuckyTactics

private theorem modeWatchSlice_relocate {F_cur : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat}
    (hvars : k.cur_vars ≤ k'.cur_vars) (hdm : k'.dense_mode = k.dense_mode)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ idx < rem, k'.wstk[p' + idx]? = k.wstk[p + idx]?)
    (h : if k.dense_mode = 0#64 then WatchSliceOk F_cur k lit p rem
         else DenseWatchSliceOk F_cur k lit p rem) :
    if k'.dense_mode = 0#64 then WatchSliceOk F_cur k' lit p' rem
    else DenseWatchSliceOk F_cur k' lit p' rem := by
  have hent : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; exact fun _ x => x
  by_cases hc : k.dense_mode = 0#64 <;>
    simp only [hdm, hc, ↓reduceIte] at h ⊢
  · exact h.fbl_relocate hent hvars hsub hwstk
  · exact h.fbl_relocate hent hvars hsub hwstk

private theorem modeWatchSlice_bin_tail' {F_cur : List (List Nat)} {k : FullCoreState}
    {src p rem : Nat} {w0 : BitVec 32}
    (hsl : if k.dense_mode = 0#64 then WatchSliceOk F_cur k src p rem
           else DenseWatchSliceOk F_cur k src p rem)
    (hpos : 0 < rem) (hp : k.wstk[p]? = some w0)
    (hbin : (w0 &&& 0x80000000#32) ≠ 0#32) :
    if k.dense_mode = 0#64 then WatchSliceOk F_cur k src (p + 1) (rem - 1)
    else DenseWatchSliceOk F_cur k src (p + 1) (rem - 1) := by
  by_cases hdm : k.dense_mode = 0#64 <;> simp only [hdm, ↓reduceIte] at hsl ⊢
  · cases hsl with
    | empty => omega
    | bin _ _ _ _ _ hrest => exact hrest
    | large hp0 _ hfl _ _ _ => rw [hp] at hp0; cases hp0; exact absurd hfl hbin
  · cases hsl with
    | empty => omega
    | bin _ _ _ _ _ hrest => exact hrest
    | occ hp0 _ hfl _ _ _ _ => rw [hp] at hp0; cases hp0; exact absurd hfl hbin

private theorem modeWatchSlice_large_tail' {F_cur : List (List Nat)} {k : FullCoreState}
    {src p rem : Nat} {w0 : BitVec 32}
    (hsl : if k.dense_mode = 0#64 then WatchSliceOk F_cur k src p rem
           else DenseWatchSliceOk F_cur k src p rem)
    (hpos : 0 < rem) (hp : k.wstk[p]? = some w0)
    (hlg : (w0 &&& 0x80000000#32) = 0#32) :
    2 ≤ rem ∧
    (if k.dense_mode = 0#64 then WatchSliceOk F_cur k src (p + 2) (rem - 2)
     else DenseWatchSliceOk F_cur k src (p + 2) (rem - 2)) := by
  by_cases hdm : k.dense_mode = 0#64 <;> simp only [hdm, ↓reduceIte] at hsl ⊢
  · cases hsl with
    | empty => omega
    | bin hp0 hfl _ _ _ _ => rw [hp] at hp0; cases hp0; exact absurd hlg hfl
    | large _ _ _ _ _ hrest => exact ⟨by omega, by simpa using hrest⟩
  · cases hsl with
    | empty => omega
    | bin hp0 hfl _ _ _ _ => rw [hp] at hp0; cases hp0; exact absurd hlg hfl
    | occ _ _ _ _ _ _ hrest => exact ⟨by omega, by simpa using hrest⟩

private theorem modeWatchSlice_copy_bin {F_cur : List (List Nat)} {k : FullCoreState}
    {wstk_q wstk' : List (BitVec 32)} {lit off q p rem : Nat} {w0 : BitVec 32}
    (hq : off ≤ q) (hpos : 0 < rem)
    (hp0 : k.wstk[p]? = some w0) (hbin : (w0 &&& 0x80000000#32) ≠ 0#32)
    (hw_q : ∀ idx < q - off, wstk'[off + idx]? = wstk_q[off + idx]?)
    (hw_new : wstk'[q]? = some w0)
    (hsl_q : if k.dense_mode = 0#64 then
               WatchSliceOk F_cur { k with wstk := wstk_q } lit off (q - off)
             else DenseWatchSliceOk F_cur { k with wstk := wstk_q } lit off (q - off))
    (hsl_p : if k.dense_mode = 0#64 then WatchSliceOk F_cur k lit p rem
             else DenseWatchSliceOk F_cur k lit p rem) :
    let k' : FullCoreState := { k with wstk := wstk' }
    if k'.dense_mode = 0#64 then WatchSliceOk F_cur k' lit off (q + 1 - off)
    else DenseWatchSliceOk F_cur k' lit off (q + 1 - off) := by
  intro k'
  have hrel : if k'.dense_mode = 0#64 then WatchSliceOk F_cur k' lit off (q - off)
      else DenseWatchSliceOk F_cur k' lit off (q - off) :=
    modeWatchSlice_relocate (k := { k with wstk := wstk_q }) (k' := k')
      (p := off) (p' := off) (Nat.le_refl _) rfl (fun _ r => r) hw_q hsl_q
  have hq1 : off + (q - off) = q := by omega
  have hq_sub : q + 1 - off = (q - off) + 1 := by omega
  by_cases hc : k.dense_mode = 0#64 <;>
    simp only [hc, k', ↓reduceIte] at hrel hsl_p ⊢ <;> rw [hq_sub]
  · cases hsl_p with
    | empty => omega
    | bin hp hflag hne hlt hent _ =>
      rw [hp0] at hp; cases hp
      exact hrel.fbl_append_slice
        (WatchSliceOk.bin (by simpa [hq1] using hw_new) hflag hne hlt hent .empty)
    | large hp _ hfl _ _ _ =>
      rw [hp0] at hp; cases hp; exact absurd hfl hbin
  · cases hsl_p with
    | empty => omega
    | bin hp hflag hne hlt hent _ =>
      rw [hp0] at hp; cases hp
      exact hrel.fbl_append_slice
        (DenseWatchSliceOk.bin (by simpa [hq1] using hw_new) hflag hne hlt hent .empty)
    | occ hp _ hfl _ _ _ _ =>
      rw [hp0] at hp; cases hp; exact absurd hfl hbin

private theorem modeWatchSlice_copy_large {F_cur : List (List Nat)} {k : FullCoreState}
    {wstk_q wstk' : List (BitVec 32)} {lit off q p rem : Nat} {w0 cr : BitVec 32}
    (hq : off ≤ q) (hpos : 0 < rem)
    (hp0 : k.wstk[p]? = some w0) (hp1 : k.wstk[p + 1]? = some cr)
    (hlg : (w0 &&& 0x80000000#32) = 0#32)
    (hw_q : ∀ idx < q - off, wstk'[off + idx]? = wstk_q[off + idx]?)
    (hw_new0 : wstk'[q]? = some w0) (hw_new1 : wstk'[q + 1]? = some cr)
    (hsl_q : if k.dense_mode = 0#64 then
               WatchSliceOk F_cur { k with wstk := wstk_q } lit off (q - off)
             else DenseWatchSliceOk F_cur { k with wstk := wstk_q } lit off (q - off))
    (hsl_p : if k.dense_mode = 0#64 then WatchSliceOk F_cur k lit p rem
             else DenseWatchSliceOk F_cur k lit p rem) :
    let k' : FullCoreState := { k with wstk := wstk' }
    if k'.dense_mode = 0#64 then WatchSliceOk F_cur k' lit off (q + 2 - off)
    else DenseWatchSliceOk F_cur k' lit off (q + 2 - off) := by
  intro k'
  have hrel : if k'.dense_mode = 0#64 then WatchSliceOk F_cur k' lit off (q - off)
      else DenseWatchSliceOk F_cur k' lit off (q - off) :=
    modeWatchSlice_relocate (k := { k with wstk := wstk_q }) (k' := k')
      (p := off) (p' := off) (Nat.le_refl _) rfl (fun _ r => r) hw_q hsl_q
  have hq1 : off + (q - off) = q := by omega
  have hq_sub : q + 2 - off = (q - off) + 2 := by omega
  by_cases hc : k.dense_mode = 0#64 <;>
    simp only [hc, k', ↓reduceIte] at hrel hsl_p ⊢ <;> rw [hq_sub]
  · cases hsl_p with
    | empty => omega
    | bin hp hfl _ _ _ _ =>
      rw [hp0] at hp; cases hp; exact absurd hlg hfl
    | large hp hpc hflag hlt href _ =>
      rw [hp0] at hp; rw [hp1] at hpc; cases hp; cases hpc
      exact hrel.fbl_append_slice
        (WatchSliceOk.large (by simpa [hq1] using hw_new0)
          (by simpa [hq1] using hw_new1) hflag hlt href .empty)
  · cases hsl_p with
    | empty => omega
    | bin hp hfl _ _ _ _ =>
      rw [hp0] at hp; cases hp; exact absurd hlg hfl
    | occ hp hpc hflag hsz hlt href _ =>
      rw [hp0] at hp; rw [hp1] at hpc; cases hp; cases hpc
      exact hrel.fbl_append_slice
        (DenseWatchSliceOk.occ (by simpa [hq1] using hw_new0)
          (by simpa [hq1] using hw_new1) hflag hsz hlt href .empty)

theorem full_add_bin_wp (Γ : Env) (hhas : EnvSpec Γ "full_has_bin" fullHasBinSpec)
    (halvl : EnvSpec Γ "full_assign_lvl" fullAssignLvlSpec)
    (hwpush : EnvSpec Γ "full_watch_push" fullWatchPushSpec) :
    ∀ args m Q X, fullAddBinSpec args m Q X → Func.wp Γ full_add_bin_body args m Q X := by
  rintro ⟨h, a, b, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hcl0, hent, hm, hQ⟩
  have hcl := hlen.core_ok
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hcl.cur_vars_le; have hvl := hcl.vals_len
  have hret0 : Q (0#64, ()) m :=
    hQ 0#64 s.core.vals s.core.flags s.core.lvl s.core.rsns s.core.trl s.core.trail_pos
      s.core.trail_end s.core.unflushed s.core.wvec s.core.wstk s.core.wlen s.core.wusable
      s.core.num_binary s.core.oom s.core.inconsistent s.core.unassigned s.scratch.phases
      s.scratch.wsort m hlen hw (Or.inl rfl) (fun _ => rfl) (fun h2 => by cases h2)
      (fun h2 => by cases h2) hm
  fbl_group
  · exact hret0
  · exact hret0
  · exact hret0
  · exact hret0
  · exact hret0
  · have ha_lt : a.toNat < 2 * s.core.cur_vars := by c0_bound
    have hb_lt : b.toNat < 2 * s.core.cur_vars := by c0_bound
    have hne_neg : a ≠ b ^^^ 1#32 := by c0_bound
    have hent_ab := hent ha_lt hb_lt
    have hdom_a := hw.vals_domain a.toNat ha_lt
    have hdom_b := hw.vals_domain b.toNat hb_lt
    refine wp_join_group
      (fun () mJ => mJ = m ∧
        ¬ (s.core.vals[a.toNat]?.getD 0#8 = 0xFF#8 ∧
           s.core.vals[b.toNat]?.getD 0#8 = 0xFF#8) ∧
        s.core.vals[a.toNat]?.getD 0#8 ≠ 1#8 ∧
        s.core.vals[b.toNat]?.getD 0#8 ≠ 1#8)
      ?_ (fun J hJ => by
        have ha_pos : s.core.vals[a.toNat]?.getD 0#8 ≠ 1#8 := by
          have h0 : BitVec.slt 0#32
              (BitVec.signExtend 32 (s.core.vals[a.toNat]'(by omega))) = false := by assumption
          intro heq; rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at heq
          rw [heq] at h0; revert h0; decide
        have hb_pos : s.core.vals[b.toNat]?.getD 0#8 ≠ 1#8 := by
          have h0 : BitVec.slt 0#32
              (BitVec.signExtend 32 (s.core.vals[b.toNat]'(by omega))) = false := by assumption
          intro heq; rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at heq
          rw [heq] at h0; revert h0; decide
        fbl_group
        · have hva_neg : s.core.vals[a.toNat]?.getD 0#8 = 0xFF#8 := by
            have hlt : BitVec.slt (BitVec.signExtend 32
                (s.core.vals[a.toNat]'(by omega))) 0#32 = true := by assumption
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hdom_a ⊢
            rcases hdom_a with h | h | h <;> rw [h] at hlt
            · exact absurd hlt (by decide)
            · exact absurd hlt (by decide)
            · exact h
          have hvb_neg : s.core.vals[b.toNat]?.getD 0#8 = 0xFF#8 := by
            have hlt : BitVec.slt (BitVec.signExtend 32
                (s.core.vals[b.toNat]'(by omega))) 0#32 = true := by assumption
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hdom_b ⊢
            rcases hdom_b with h | h | h <;> rw [h] at hlt
            · exact absurd hlt (by decide)
            · exact absurd hlt (by decide)
            · exact h
          have hFcur_unsat : (cnfOfClauses F_cur).Unsat := by
            refine unsat_of_entails_nil (entails_of_mem_or_false hent_ab fun l hl => Or.inr ?_)
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
            rcases hl with rfl | rfl
            · obtain ⟨ia, hia, haeq⟩ := (hw.vals_false_iff _ ha_lt).mp hva_neg
              have hs := hw.level0_sound ia hia (by have := hw.lvl_le ia hia; omega)
              rwa [haeq] at hs
            · obtain ⟨ib, hib, hbeq⟩ := (hw.vals_false_iff _ hb_lt).mp hvb_neg
              have hs := hw.level0_sound ib hib (by have := hw.lvl_le ib hib; omega)
              rwa [hbeq] at hs
          have hF0_unsat : F0.Unsat := hw.ext_sound.2 hFcur_unsat
          have hlen_inc : ({ s with core := { s.core with inconsistent := 1#64 } } :
              FullState).LengthsOk c := ⟨{ hcl with }, hlen.scratch_ok⟩
          have hw' : FullWitnessInv c F0 F_cur { s.core with inconsistent := 1#64 } :=
            { hw with
              inconsistent_sound := fun _ => hFcur_unsat
              arena := { hw.arena with len_ok := hw.arena.len_ok }
              watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }
          exact hQ 20#64 s.core.vals s.core.flags s.core.lvl s.core.rsns s.core.trl
            s.core.trail_pos s.core.trail_end s.core.unflushed s.core.wvec s.core.wstk
            s.core.wlen s.core.wusable s.core.num_binary s.core.oom 1#64 s.core.unassigned
            s.scratch.phases s.scratch.wsort _ hlen_inc hw'
            (Or.inr (Or.inr (Or.inr rfl))) (fun h0 => by cases h0) (fun h2 => by cases h2)
            (fun _ => ⟨hF0_unsat, rfl⟩) (by assumption)
        · have hnb : s.core.vals[b.toNat]?.getD 0#8 ≠ 0xFF#8 := by
            have h0 : BitVec.slt (BitVec.signExtend 32
                (s.core.vals[b.toNat]'(by omega))) 0#32 = false := by assumption
            intro heq; rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at heq
            rw [heq] at h0; revert h0; decide
          exact hJ () _ ⟨rfl, fun ⟨_, hb⟩ => hnb hb, ha_pos, hb_pos⟩
        · have hna : s.core.vals[a.toNat]?.getD 0#8 ≠ 0xFF#8 := by
            have h0 : BitVec.slt (BitVec.signExtend 32
                (s.core.vals[a.toNat]'(by omega))) 0#32 = false := by assumption
            intro heq; rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at heq
            rw [heq] at h0; revert h0; decide
          exact hJ () _ ⟨rfl, fun ⟨ha, _⟩ => hna ha, ha_pos, hb_pos⟩)
    rintro _ _ mJ ⟨rfl, hnot_both, ha_pos, hb_pos⟩
    have hassign_lit : ∀ (lit : BitVec 32), lit.toNat < 2 * s.core.cur_vars →
        s.core.vals[lit.toNat]?.getD 0#8 = 0#8 →
        (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat]) →
        wp Γ Q X (Expr.call (as := [i64, i32, i32, i32]) (bs := []) "full_assign_lvl"
          (Arg.var c.hdr, Arg.var lit, Arg.imm (4294967295#32 : Val i32),
            Arg.imm (0#32 : Val i32), ())
          fun _ => Expr.ret (Arg.imm (1#64 : Val i64), ())) mJ := by
      intro lit hlit hun hunit
      c0_call halvl
      refine ⟨c, s, R, rfl, hlen, hm, ?_⟩
      have hte_lt : s.core.trail_end < c.max_vars := by
        have := hw.trail_end_lt_of_unassigned hlit hun; omega
      have hnot_cond : ¬ (s.core.cur_vars ≤ lit.toNat / 2 ∨
          c.max_vars ≤ s.core.trail_end ∨ s.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8) := by
        intro h; rcases h with h1 | h2 | h3
        · omega
        · omega
        · exact h3 hun
      rw [ite_eq_right hnot_cond]
      dsimp only
      intro flags' unassigned' phases' m' hfll hphl _ hlen' hm'
      obtain ⟨_, hw'⟩ :=
        fbl_assignLevel0_preserves_fullWitness hlen hw hcl0 hfll hphl hlit hun hunit
      fbl_group
      refine hQ 1#64 _ flags' _ _ _ _ _ _ s.core.wvec s.core.wstk s.core.wlen s.core.wusable
        s.core.num_binary s.core.oom s.core.inconsistent unassigned' phases' s.scratch.wsort m'
        hlen' hw' (Or.inr (Or.inl rfl)) (fun h0 => by cases h0) (fun h2 => by cases h2)
        (fun h2 => by cases h2) hm'
    fbl_group
    refine wp_join_group (fun _ mK => mK = mJ ∧
      (s.core.vals[a.toNat]?.getD 0#8 = 0xFF#8 ∨ a = b))
      ?_ (fun J hJ => by
        fbl_group
        · have hva_neg : s.core.vals[a.toNat]?.getD 0#8 = 0xFF#8 := by
            have hlt : BitVec.slt (BitVec.signExtend 32
                (s.core.vals[a.toNat]'(by omega))) 0#32 = true := by assumption
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hdom_a ⊢
            rcases hdom_a with h | h | h <;> rw [h] at hlt
            · exact absurd hlt (by decide)
            · exact absurd hlt (by decide)
            · exact h
          exact hJ () _ ⟨rfl, Or.inl hva_neg⟩
        · exact hJ () _ ⟨rfl, Or.inr (by assumption)⟩
        · have hna_neg : s.core.vals[a.toNat]?.getD 0#8 ≠ 0xFF#8 := by
            have h0 : BitVec.slt (BitVec.signExtend 32
                (s.core.vals[a.toNat]'(by omega))) 0#32 = false := by assumption
            intro heq; rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at heq
            rw [heq] at h0; revert h0; decide
          have hva0 : s.core.vals[a.toNat]?.getD 0#8 = 0#8 := by
            rcases hdom_a with h | h | h <;> first | exact h | contradiction
          have hvb_neg : s.core.vals[b.toNat]?.getD 0#8 = 0xFF#8 := by
            have hlt : BitVec.slt (BitVec.signExtend 32
                (s.core.vals[b.toNat]'(by omega))) 0#32 = true := by assumption
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hdom_b ⊢
            rcases hdom_b with h | h | h <;> rw [h] at hlt
            · exact absurd hlt (by decide)
            · exact absurd hlt (by decide)
            · exact h
          have hunit_a : (cnfOfClauses F_cur).EntailsClause (cnfClause [a.toNat]) := by
            refine entails_of_mem_or_false hent_ab fun l hl => ?_
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
            rcases hl with rfl | rfl
            · exact Or.inl (by simp)
            · obtain ⟨ib, hib, hbeq⟩ := (hw.vals_false_iff _ hb_lt).mp hvb_neg
              have hs := hw.level0_sound ib hib (by have := hw.lvl_le ib hib; omega)
              right; rwa [hbeq] at hs
          exact hassign_lit a ha_lt hva0 hunit_a
        · have hna_neg : s.core.vals[a.toNat]?.getD 0#8 ≠ 0xFF#8 := by
            have h0 : BitVec.slt (BitVec.signExtend 32
                (s.core.vals[a.toNat]'(by omega))) 0#32 = false := by assumption
            intro heq; rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at heq
            rw [heq] at h0; revert h0; decide
          have hva0 : s.core.vals[a.toNat]?.getD 0#8 = 0#8 := by
            rcases hdom_a with h | h | h <;> first | exact h | contradiction
          c0_call hhas
          refine ⟨c, F0, s, R, rfl, ⟨hlen, ⟨F_cur, hw⟩⟩, hm, ?_⟩
          intro r hr
          fbl_group
          · exact hret0
          · have hwpc := fbl_bv32_mask_bin b (by omega)
            have hwpc1 := fbl_bv32_mask_bin a (by omega)
            refine wp_join_group
              (fun _ mO => ∃ wvecO wstkO wlenO wuO wsortO,
                let sO : FullState :=
                  { s with
                    core := { s.core with wvec := wvecO, wstk := wstkO,
                                          wlen := wlenO, wusable := wuO }
                    scratch := { s.scratch with wsort := wsortO } }
                sO.LengthsOk c ∧ ModeWatchesInv F_cur sO.core ∧ (FullMem c sO ⋆ R) mO)
              ?_ (fun J hJ => by
                c0_call hwpush
                refine ⟨c, s, R, rfl, hlen, hw.watches.layout, fun _ => hwpc.1,
                  fun h2 => absurd h2 (by decide), hm, ?_⟩
                dsimp only
                intro ok1 wvec1 wstk1 wlen1 wu1 wsort1 m1 hlen1 hlay1 hother1 hok1t hok1f hm1
                let s1 : FullState :=
                  { s with
                    core := { s.core with wvec := wvec1, wstk := wstk1,
                                          wlen := wlen1, wusable := wu1 }
                    scratch := { s.scratch with wsort := wsort1 } }
                fbl_group
                · obtain ⟨_, _, hsz1, hpref1, hw0_1, _⟩ := hok1t (by assumption)
                  have hok1 : ok1 = true := by assumption
                  have hw1_ok : ModeWatchesInv F_cur s1.core :=
                    fbl_watchPush_bin_preserves_modeWatches (ok := ok1) hw.watches hlay1 rfl rfl
                      (fun _ r => r) ⟨hwpc.2.1, hwpc.1, hwpc.2.2 ▸ hb_lt, hwpc.2.2 ▸ hent_ab⟩
                      hother1 (fun _ => ⟨ha_lt, hsz1, hpref1, hw0_1⟩)
                      (fun hf => by rw [hok1] at hf; cases hf)
                  c0_call hwpush
                  refine ⟨c, s1, R, rfl, hlen1, hlay1, fun _ => hwpc1.1,
                    fun h2 => absurd h2 (by decide), hm1, ?_⟩
                  dsimp only
                  intro ok2 wvec2 wstk2 wlen2 wu2 wsort2 m2 hlen2 hlay2 hother2 hok2t hok2f hm2
                  let s2 : FullState :=
                    { s1 with
                      core := { s1.core with wvec := wvec2, wstk := wstk2, wlen := wlen2,
                                             wusable := wu2 }
                      scratch := { s.scratch with wsort := wsort2 } }
                  fbl_group
                  · obtain ⟨_, _, hsz2, hpref2, hw0_2, _⟩ := hok2t (by assumption)
                    have hok2 : ok2 = true := by assumption
                    have hw2_ok : ModeWatchesInv F_cur s2.core :=
                      fbl_watchPush_bin_preserves_modeWatches (ok := ok2) hw1_ok hlay2 rfl rfl
                        (fun _ r => r) ⟨hwpc1.2.1, hwpc1.1, hwpc1.2.2 ▸ ha_lt,
                          hwpc1.2.2 ▸ fbl_entailsClause_swap2 hent_ab⟩
                        hother2 (fun _ => ⟨hb_lt, hsz2, hpref2, hw0_2⟩)
                        (fun hf => by rw [hok2] at hf; cases hf)
                    have hlen2' : ({ s2 with core := { s2.core with
                        num_binary := s.core.num_binary + 1#64 } } : FullState).LengthsOk c :=
                      ⟨{ hlen2.core_ok with }, hlen2.scratch_ok⟩
                    have hw2' : FullWitnessInv c F0 F_cur
                        { s2.core with num_binary := s.core.num_binary + 1#64 } :=
                      { hw with
                        arena := { hw.arena with len_ok := hw.arena.len_ok }
                        watches := hw2_ok.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }
                    exact hQ 1#64 s.core.vals s.core.flags s.core.lvl s.core.rsns s.core.trl
                      s.core.trail_pos s.core.trail_end s.core.unflushed wvec2 wstk2 wlen2 wu2
                      (s.core.num_binary + 1#64) s.core.oom s.core.inconsistent s.core.unassigned
                      s.scratch.phases wsort2 _ hlen2' hw2' (Or.inr (Or.inl rfl))
                      (fun h0 => by cases h0) (fun h2 => by cases h2) (fun h2 => by cases h2)
                      (by assumption)
                  · have hw2_fail : ModeWatchesInv F_cur s2.core := by
                      refine fbl_watchPush_fail_preserves_modeWatches hw1_ok hlay2 rfl rfl
                        (fun _ r => r) ?_
                      intro l hl
                      by_cases hle : l = b.toNat
                      · subst hle; exact (hok2f (by assumption)).1 hb_lt
                      · exact hother2 l hl hle
                    exact hJ () m2 ⟨wvec2, wstk2, wlen2, wu2, wsort2, hlen2, hw2_fail, hm2⟩
                · have hw1_fail : ModeWatchesInv F_cur s1.core := by
                    refine fbl_watchPush_fail_preserves_modeWatches hw.watches hlay1 rfl rfl
                      (fun _ r => r) ?_
                    intro l hl
                    by_cases hle : l = a.toNat
                    · subst hle; exact (hok1f (by assumption)).1 ha_lt
                    · exact hother1 l hl hle
                  exact hJ () m1 ⟨wvec1, wstk1, wlen1, wu1, wsort1, hlen1, hw1_fail, hm1⟩)
            rintro _ _ mO ⟨wvecO, wstkO, wlenO, wuO, wsortO, hlenO, hwO, hmO⟩
            have hlenO' : ({ s with
                core := { s.core with wvec := wvecO, wstk := wstkO, wlen := wlenO,
                                      wusable := wuO, oom := 1#64 }
                scratch := { s.scratch with wsort := wsortO } } :
                FullState).LengthsOk c := ⟨{ hlenO.core_ok with }, hlenO.scratch_ok⟩
            have hwO' : FullWitnessInv c F0 F_cur
                { s.core with wvec := wvecO, wstk := wstkO, wlen := wlenO,
                              wusable := wuO, oom := 1#64 } :=
              { hw with
                arena := { hw.arena with len_ok := hw.arena.len_ok }
                watches := hwO.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }
            fbl_group
            exact hQ 2#64 s.core.vals s.core.flags s.core.lvl s.core.rsns s.core.trl
              s.core.trail_pos s.core.trail_end s.core.unflushed wvecO wstkO
              wlenO wuO s.core.num_binary 1#64 s.core.inconsistent
              s.core.unassigned s.scratch.phases wsortO _ hlenO' hwO'
              (Or.inr (Or.inr (Or.inl rfl))) (fun h0 => by cases h0)
              (fun _ => rfl) (fun h2 => by cases h2) (by assumption))
    rintro _ _ mK ⟨rfl, hcond⟩
    have hvb0 : s.core.vals[b.toNat]?.getD 0#8 = 0#8 := by
      have hnb : s.core.vals[b.toNat]?.getD 0#8 ≠ 0xFF#8 := by
        rcases hcond with hva_neg | rfl
        · exact fun hb => hnot_both ⟨hva_neg, hb⟩
        · exact fun hb => hnot_both ⟨hb, hb⟩
      rcases hdom_b with h | h | h <;> first | exact h | contradiction
    have hunit_b : (cnfOfClauses F_cur).EntailsClause (cnfClause [b.toNat]) := by
      rcases hcond with hva_neg | rfl
      · refine entails_of_mem_or_false hent_ab fun l hl => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl
        · obtain ⟨ia, hia, haeq⟩ := (hw.vals_false_iff _ ha_lt).mp hva_neg
          have hs := hw.level0_sound ia hia (by have := hw.lvl_le ia hia; omega)
          right; rwa [haeq] at hs
        · exact Or.inl (by simp)
      · refine entails_of_mem_or_false hent_ab fun l hl => Or.inl ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl ⊢
        rcases hl with rfl | rfl <;> rfl
    exact hassign_lit b hb_lt hvb0 hunit_b

theorem full_set_inactive_wp (Γ : Env) :
    ∀ args m Q X, fullSetInactiveSpec args m Q X → Func.wp Γ full_set_inactive_body args m Q X := by
  rintro ⟨h, v, flag, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  have hcl := hlen.core_ok
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hcl.cur_vars_le; have hfll := hcl.flags_len; have hvl := hcl.vals_len
  fbl_group
  · rw [ite_eq_left (by c0_bound)] at hQ; exact hQ
  · have hv_lt : v.toNat < s.core.cur_vars := by c0_bound
    rw [ite_eq_right (by omega)] at hQ
    have h2v : ((v.setWidth 64) <<< (1 : Nat)).toNat = 2 * v.toNat := by
      have : v.toNat < 2 ^ 30 := by omega
      bv_omega
    refine wp_join_group
      (fun _ mJ => ∃ unass',
        (FullMem c { s with core := { s.core with unassigned := unass' } } ⋆ R) mJ)
      ?_ (fun J hJ => by
        fbl_group
        · exact hJ () _ ⟨_, by assumption⟩
        · exact hJ () _ ⟨_, by assumption⟩
        · exact hJ () _ ⟨_, by assumption⟩
        · exact hJ () _ ⟨_, by assumption⟩)
    rintro _ _ mJ ⟨unass', hmJ⟩
    fbl_group
    have hvn : (v.setWidth 64).toNat = v.toNat := by bv_omega
    exact hQ (s.core.flags.set (v.setWidth 64).toNat
      (s.core.flags[(v.setWidth 64).toNat]'(by rw [hfll, hvn]; omega) &&& ~~~1 ||| flag)) unass' m
      (by rw [List.length_set, hfll]) (by assumption)

theorem full_add_unit_wp (Γ : Env)
    (hbt : EnvSpec Γ "full_backtrack" fullBacktrackSpec)
    (halvl : EnvSpec Γ "full_assign_lvl" fullAssignLvlSpec) :
    ∀ args m Q X, fullAddUnitSpec args m Q X → Func.wp Γ full_add_unit_body args m Q X := by
  rintro ⟨h, lit, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hent, hm, hQ⟩
  have hcl := hlen.core_ok
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  fbl_group
  · refine wp_join_group
      (fun _ mJ => ∃ valsJ lvlJ rsnsJ trlJ tpJ teJ propJ clJ unassJ taJ baJ ptJ pbJ hpJ psJ hlJ
          qsiJ qssJ,
        let sJ : FullState :=
          { s with
            core := { s.core with
              vals := valsJ, lvl := lvlJ, rsns := rsnsJ, trl := trlJ, trail_pos := tpJ,
              trail_end := teJ, propagated := propJ, cur_level := clJ, unassigned := unassJ }
            scratch := { s.scratch with
              target_assigned := taJ, best_assigned := baJ, phases_target := ptJ,
              phases_best := pbJ, heap := hpJ, pos := psJ, heap_len := hlJ,
              q_search_idx := qsiJ, q_search_stamp := qssJ } }
        sJ.LengthsOk c ∧ FullWitnessInv c F0 F_cur sJ.core ∧ clJ = 0 ∧ (FullMem c sJ ⋆ R) mJ)
      ?_ (fun J hJ => by
        fbl_group
        · c0_call hbt
          refine ⟨c, s, R, rfl, hlen, hw.trail_lits_lt, hm, ?_⟩
          have hpos : ¬ s.core.cur_level ≤ BitVec.toNat (0 : BitVec 64) := by c0_bound
          rw [ite_eq_right hpos]
          dsimp only
          intro vals' lvl' rsns' trl' tp' te' prop' unass' ta' ba' pt' pb' hp' ps' hl' qsi'
            qss' m' hlen' _ _ _ _ hw' hm'
          exact hJ () m' ⟨vals', lvl', rsns', trl', tp', te', prop', 0, unass', ta', ba', pt',
            pb', hp', ps', hl', qsi', qss', hlen', hw' F0 F_cur hw, rfl, hm'⟩
        · have hcl0 : s.core.cur_level = 0 := by
            have := hw.cur_level_le; have := hcl.trail_end_le; have := hcl.cur_vars_le
            c0_bound
          have hs_self : ({ s with
              core := { s.core with
                vals := s.core.vals, lvl := s.core.lvl, rsns := s.core.rsns, trl := s.core.trl,
                trail_pos := s.core.trail_pos, trail_end := s.core.trail_end,
                propagated := s.core.propagated, cur_level := s.core.cur_level,
                unassigned := s.core.unassigned }
              scratch := { s.scratch with
                target_assigned := s.scratch.target_assigned,
                best_assigned := s.scratch.best_assigned,
                phases_target := s.scratch.phases_target, phases_best := s.scratch.phases_best,
                heap := s.scratch.heap, pos := s.scratch.pos, heap_len := s.scratch.heap_len,
                q_search_idx := s.scratch.q_search_idx,
                q_search_stamp := s.scratch.q_search_stamp } } : FullState) = s := by cases s; rfl
          exact hJ () m ⟨s.core.vals, s.core.lvl, s.core.rsns, s.core.trl, s.core.trail_pos,
            s.core.trail_end, s.core.propagated, s.core.cur_level, s.core.unassigned,
            s.scratch.target_assigned, s.scratch.best_assigned, s.scratch.phases_target,
            s.scratch.phases_best, s.scratch.heap, s.scratch.pos, s.scratch.heap_len,
            s.scratch.q_search_idx, s.scratch.q_search_stamp,
            by simpa only [hs_self] using hlen, by simpa only [hs_self] using hw, hcl0,
            by simpa only [hs_self] using hm⟩)
    rintro _ _ mJ ⟨valsJ, lvlJ, rsnsJ, trlJ, tpJ, teJ, propJ, clJ, unassJ, taJ, baJ, ptJ, pbJ,
      hpJ, psJ, hlJ, qsiJ, qssJ, hlenJ, hwJ, hclJ0, hmJ⟩
    let sJ : FullState :=
      { s with
        core := { s.core with
          vals := valsJ, lvl := lvlJ, rsns := rsnsJ, trl := trlJ, trail_pos := tpJ,
          trail_end := teJ, propagated := propJ, cur_level := clJ, unassigned := unassJ }
        scratch := { s.scratch with
          target_assigned := taJ, best_assigned := baJ, phases_target := ptJ,
          phases_best := pbJ, heap := hpJ, pos := psJ, heap_len := hlJ,
          q_search_idx := qsiJ, q_search_stamp := qssJ } }
    change sJ.LengthsOk c at hlenJ
    change FullWitnessInv c F0 F_cur sJ.core at hwJ
    change (FullMem c sJ ⋆ R) mJ at hmJ
    have hclJ := hlenJ.core_ok
    have hcvJ := hclJ.cur_vars_le; have hvlJ := hclJ.vals_len
    have hshr1 : (lit >>> (1 : Nat)).toNat = lit.toNat / 2 := by
      simp [Nat.shiftRight_eq_div_pow]
    fbl_group
    · exact hQ false valsJ s.core.flags lvlJ rsnsJ trlJ tpJ teJ propJ clJ s.core.unflushed
        s.core.inconsistent unassJ s.scratch.phases taJ baJ ptJ pbJ hpJ psJ hlJ qsiJ qssJ mJ
        hlenJ hwJ hclJ0 (fun _ => Or.inl (by change sJ.core.cur_vars ≤ _; c0_bound))
        (fun hf => by cases hf) hmJ
    · have hv_lt : lit.toNat / 2 < s.core.cur_vars := by
        change lit.toNat / 2 < sJ.core.cur_vars; c0_bound
      exact hQ true valsJ s.core.flags lvlJ rsnsJ trlJ tpJ teJ propJ clJ s.core.unflushed
        s.core.inconsistent unassJ s.scratch.phases taJ baJ ptJ pbJ hpJ psJ hlJ qsiJ qssJ mJ
        hlenJ hwJ hclJ0 (fun ht => by cases ht) (fun _ => hv_lt) hmJ
    · have hv_lt : lit.toNat / 2 < s.core.cur_vars := by
        change lit.toNat / 2 < sJ.core.cur_vars; c0_bound
      have hlit_lt : lit.toNat < 2 * sJ.core.cur_vars := by omega
      have hdom := hwJ.vals_domain lit.toNat hlit_lt
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hdom
      have hva_neg : sJ.core.vals[lit.toNat]?.getD 0#8 = 0xFF#8 := by
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
        exact (fbl_bv8_vals_pos hdom).2.mp (by assumption)
      have hent_lit := hent hv_lt
      have hFcur_unsat : (cnfOfClauses F_cur).Unsat := by
        refine unsat_of_entails_nil (entails_of_mem_or_false hent_lit fun l hl => Or.inr ?_)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        subst hl
        obtain ⟨i, hi, heq⟩ := (hwJ.vals_false_iff _ hlit_lt).mp hva_neg
        have hs := hwJ.level0_sound i hi
          (by have := hwJ.lvl_le i hi; simp only [sJ, hclJ0] at *; omega)
        rwa [heq] at hs
      have hF0_unsat : F0.Unsat := hwJ.ext_sound.2 hFcur_unsat
      have hlen_inc : ({ sJ with core := { sJ.core with inconsistent := 1#64 } } :
          FullState).LengthsOk c := ⟨{ hclJ with }, hlenJ.scratch_ok⟩
      have hwJ' : FullWitnessInv c F0 F_cur { sJ.core with inconsistent := 1#64 } :=
        { hwJ with
          inconsistent_sound := fun _ => hFcur_unsat
          arena := { hwJ.arena with len_ok := hwJ.arena.len_ok }
          watches := hwJ.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }
      exact hQ false valsJ s.core.flags lvlJ rsnsJ trlJ tpJ teJ propJ clJ s.core.unflushed
        1#64 unassJ s.scratch.phases taJ baJ ptJ pbJ hpJ psJ hlJ qsiJ qssJ _
        hlen_inc hwJ' hclJ0 (fun _ => Or.inr ⟨hF0_unsat, rfl⟩) (fun hf => by cases hf)
        (by assumption)
    · have hv_lt : lit.toNat / 2 < s.core.cur_vars := by
        change lit.toNat / 2 < sJ.core.cur_vars; c0_bound
      have hlit_lt : lit.toNat < 2 * sJ.core.cur_vars := by omega
      have hdom := hwJ.vals_domain lit.toNat hlit_lt
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hdom
      have hval0 : sJ.core.vals[lit.toNat]?.getD 0#8 = 0#8 := by
        have hpos_f : BitVec.slt 0#32
            (BitVec.signExtend 32 (sJ.core.vals[lit.toNat]'(by omega))) = false := by assumption
        have hneg_f : BitVec.slt (BitVec.signExtend 32
            (sJ.core.vals[lit.toNat]'(by omega))) 0#32 = false := by assumption
        have hfb := fbl_bv8_vals_pos hdom
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
        rcases hdom with h | h | h
        · exact h
        · exact absurd (hfb.1.mpr h) (by rw [hpos_f]; decide)
        · exact absurd (hfb.2.mpr h) (by rw [hneg_f]; decide)
      have hent_lit := hent hv_lt
      c0_call halvl
      refine ⟨c, sJ, R, rfl, hlenJ, hmJ, ?_⟩
      have hte_lt : sJ.core.trail_end < c.max_vars := by
        have := hwJ.trail_end_lt_of_unassigned hlit_lt hval0; omega
      have hnot_cond : ¬ (sJ.core.cur_vars ≤ lit.toNat / 2 ∨
          c.max_vars ≤ sJ.core.trail_end ∨ sJ.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8) := by
        intro h; rcases h with h1 | h2 | h3
        · omega
        · omega
        · exact h3 hval0
      rw [ite_eq_right hnot_cond]
      dsimp only
      intro flags' unassigned' phases' m' hfll hphl _ hlen' hm'
      obtain ⟨_, hw'⟩ := fbl_assignLevel0_preserves_fullWitness hlenJ hwJ hclJ0 hfll hphl hlit_lt
        hval0 hent_lit
      exact hQ true ((sJ.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8)
        flags' (sJ.core.lvl.set (lit.toNat / 2) 0#32)
        (sJ.core.rsns.set (lit.toNat / 2) 0xFFFFFFFF#32) (sJ.core.trl.set sJ.core.trail_end lit)
        (sJ.core.trail_pos.set (lit.toNat / 2) (BitVec.ofNat 32 sJ.core.trail_end))
        (sJ.core.trail_end + 1) propJ clJ (s.core.unflushed + 1#64) s.core.inconsistent
        unassigned' phases' taJ baJ ptJ pbJ hpJ psJ hlJ qsiJ qssJ m'
        hlen' hw' hclJ0 (fun ht => by cases ht) (fun _ => hv_lt) hm'

theorem full_delete_bin_side_wp (Γ : Env) :
    ∀ args m Q X, fullDeleteBinSideSpec args m Q X →
      Func.wp Γ full_delete_bin_side_body args m Q X := by
  rintro ⟨h, lit, other, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩
  obtain ⟨F_base, hw_base⟩ := hinv.witness
  have hcl := hinv.lengths.core_ok
  have hmx := c.hmaxv; have hwc := c.hwcap; unfold dimacsBound at hmx hwc
  have hcv_le := hcl.cur_vars_le; have hwvl := hcl.wvec_len; have hwl := hcl.wstk_len_arr
  have hwle := hcl.wlen_le
  have hret_same : Q () m := hQ s.core.wvec s.core.wstk s.core.wusable m hinv.lengths
    (fun _ hw => hw) hm
  fbl_group
  · exact hret_same
  · exact hret_same
  · have hlit_lt : lit.toNat < 2 * s.core.cur_vars := by c0_bound
    have hidx0 : (lit.setWidth 64 <<< (1 : Nat)).toNat = 2 * lit.toNat := by
      have : lit.toNat < 2 ^ 30 := by omega
      bv_omega
    have hidx1 : ((lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat = 2 * lit.toNat + 1 := by
      have : lit.toNat < 2 ^ 30 := by omega
      bv_omega
    have hoff_eq : (s.core.wvec[2 * lit.toNat]'(by omega)).toNat =
        fullWatchOffCore s.core lit.toNat := by
      unfold fullWatchOffCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    have hsz_eq : (s.core.wvec[2 * lit.toNat + 1]'(by omega)).toNat =
        fullWatchSizeCore s.core lit.toNat := by
      unfold fullWatchSizeCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    have hbd_slice : fullWatchOffCore s.core lit.toNat + fullWatchSizeCore s.core lit.toNat ≤
        s.core.wlen := hw_base.watches.bounds lit.toNat hlit_lt
    have hs0 : 2 * lit.toNat % 2 ^ 64 = 2 * lit.toNat := by omega
    have h1_64 : BitVec.toNat (1 : BitVec 64) = 1 := rfl
    have hs1 : (2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = 2 * lit.toNat + 1 := by
      rw [h1_64]; omega
    have h_off : (BitVec.setWidth 64
        (s.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'(by rw [hidx0]; omega))).toNat =
        fullWatchOffCore s.core lit.toNat := by
      simp only [hidx0, BitVec.toNat_setWidth, hoff_eq]; omega
    have h_sz : (BitVec.setWidth 64
        (s.core.wvec[2 * lit.toNat + 1]'(by omega))).toNat =
        fullWatchSizeCore s.core lit.toNat := by
      simp only [BitVec.toNat_setWidth, hsz_eq]; omega
    have h_end : (BitVec.setWidth 64 s.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat] +
        BitVec.setWidth 64 s.core.wvec[(2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) %
          2 ^ 64]).toNat =
        fullWatchOffCore s.core lit.toNat + fullWatchSizeCore s.core lit.toNat := by
      simp only [hidx0, hs1, BitVec.toNat_add, BitVec.toNat_setWidth, hoff_eq, hsz_eq]; omega
    have hsz_pos : 0 < fullWatchSizeCore s.core lit.toNat := by
      refine Nat.pos_of_ne_zero fun h0 => hc (BitVec.eq_of_toNat_eq ?_)
      simp only [h1_64, Nat.mod_eq_of_lt (by omega : 2 * lit.toNat + 1 < 2 ^ 64),
        BitVec.toNat_setWidth, hsz_eq, h0]
      rfl
    let off := fullWatchOffCore s.core lit.toNat
    let sz := fullWatchSizeCore s.core lit.toNat
    let end_ := off + sz
    have h_cond_lt : (s.core.wvec[2 * lit.toNat % 2 ^ 64].toNat +
        s.core.wvec[(2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64].toNat) % 2 ^ 64 =
        end_ := by
      simp only [hs0, hs1, hoff_eq, hsz_eq]; omega
    refine wp_loop_inv
        (fun (p, q, _rem, ()) ml => ∃ wstk1 : List (BitVec 32),
          off ≤ q.toNat ∧ q.toNat ≤ p.toNat ∧ p.toNat ≤ end_ ∧ wstk1.length = c.wcap ∧
          (∀ idx, idx < off ∨ p.toNat ≤ idx → wstk1[idx]? = s.core.wstk[idx]?) ∧
          (∀ F_cur, FullWitnessInv c F0 F_cur s.core →
            (if s.core.dense_mode = 0#64 then
               WatchSliceOk F_cur { s.core with wstk := wstk1 } lit.toNat off (q.toNat - off)
             else
               DenseWatchSliceOk F_cur { s.core with wstk := wstk1 } lit.toNat off
                 (q.toNat - off)) ∧
            (if s.core.dense_mode = 0#64 then
               WatchSliceOk F_cur s.core lit.toNat p.toNat (end_ - p.toNat)
             else
               DenseWatchSliceOk F_cur s.core lit.toNat p.toNat (end_ - p.toNat))) ∧
          (FullMem c { s with core := { s.core with wstk := wstk1 } } ⋆ R) ml)
        (fun (p, _, _, ()) _ => end_ - p.toNat)
        (fun J hJ => by
          fbl_group
          have h_off_eq : (BitVec.setWidth 64
              (s.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'(by
                rw [hidx0]; omega))).toNat = off := h_off
          refine hJ _ _ ⟨s.core.wstk, h_off_eq ▸ Nat.le_refl _, le_refl _,
            by rw [h_off_eq]; omega, hwl, fun _ _ => rfl, fun F_cur hw => ?_, hm⟩
          rw [h_off_eq]
          have heq0 : off - off = 0 := Nat.sub_self off
          have heqs : end_ - off = sz := by omega
          rw [heq0, heqs]
          have hwm := hw.watches
          by_cases hdm : s.core.dense_mode = 0#64 <;>
            simp only [ModeWatchesInv, hdm, ↓reduceIte] at hwm ⊢
          · exact ⟨.empty, hwm.slices lit.toNat hlit_lt⟩
          · exact ⟨.empty, hwm.slices lit.toNat hlit_lt⟩)
        (fun J (p, q, rem, ()) ml ⟨wstk1, hq_lo, hqp, hp_hi, hwl1, hrest1, hsl1, hm1⟩ ih => ?_)
    fbl_group
    · have hp_lt : p.toNat < end_ := by rw [← h_cond_lt]; assumption
      have hrem_pos : 0 < end_ - p.toNat := by omega
      have hp_lt_cap : p.toNat < c.wcap := by omega
      have hw0_val : wstk1[p.toNat]'(by omega) = s.core.wstk[p.toNat]'(by omega) := by
        have := hrest1 p.toNat (Or.inr (le_refl _))
        rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at this
        exact Option.some.inj this
      have hw0_eq : s.core.wstk[p.toNat]? = some (s.core.wstk[p.toNat]'(by omega)) :=
        List.getElem?_eq_getElem (by omega)
      have hp1_eq : (p + 1).toNat = p.toNat + 1 := by bv_omega
      refine wp_join_group
        (fun (p', q', rem', ()) mJ => ∃ wstk2 : List (BitVec 32),
          off ≤ q'.toNat ∧ q'.toNat ≤ p'.toNat ∧ p'.toNat ≤ end_ ∧ p.toNat < p'.toNat ∧
          wstk2.length = c.wcap ∧
          (∀ idx, idx < off ∨ p'.toNat ≤ idx → wstk2[idx]? = s.core.wstk[idx]?) ∧
          (∀ F_cur, FullWitnessInv c F0 F_cur s.core →
            (if s.core.dense_mode = 0#64 then
               WatchSliceOk F_cur { s.core with wstk := wstk2 } lit.toNat off (q'.toNat - off)
             else
               DenseWatchSliceOk F_cur { s.core with wstk := wstk2 } lit.toNat off
                 (q'.toNat - off)) ∧
            (if s.core.dense_mode = 0#64 then
               WatchSliceOk F_cur s.core lit.toNat p'.toNat (end_ - p'.toNat)
             else
               DenseWatchSliceOk F_cur s.core lit.toNat p'.toNat (end_ - p'.toNat))) ∧
          (FullMem c { s with core := { s.core with wstk := wstk2 } } ⋆ R) mJ)
        (by
          rintro _ ⟨p', q', rem', ⟨⟩⟩ mJ ⟨wstk2, hq'lo, hq'p', hp'hi, hpgt, hwl2, hr2, hs2, hm2⟩
          dsimp only at hq'lo hq'p' hp'hi hpgt hr2 hs2 ⊢
          exact ih (p', q', rem', ()) mJ (by dsimp only; omega)
            ⟨wstk2, hq'lo, hq'p', hp'hi, hwl2, hr2, hs2, hm2⟩)
        (fun J1 hJ1 => by
          fbl_group
          · refine wp_join_group
              (fun (q'', rem'', ()) mJ1 => ∃ wstk2 : List (BitVec 32),
                off ≤ q''.toNat ∧ q''.toNat ≤ p.toNat + 1 ∧ wstk2.length = c.wcap ∧
                (∀ idx, idx < off ∨ p.toNat + 1 ≤ idx → wstk2[idx]? = s.core.wstk[idx]?) ∧
                (∀ F_cur, FullWitnessInv c F0 F_cur s.core →
                  if s.core.dense_mode = 0#64 then
                    WatchSliceOk F_cur { s.core with wstk := wstk2 } lit.toNat off
                      (q''.toNat - off)
                  else
                    DenseWatchSliceOk F_cur { s.core with wstk := wstk2 } lit.toNat off
                      (q''.toNat - off)) ∧
                (FullMem c { s with core := { s.core with wstk := wstk2 } } ⋆ R) mJ1)
              (by
                rintro _ ⟨q'', rem'', ⟨⟩⟩ mJ1 ⟨wstk2, hq''lo, hq''le, hwl2, hr2, hsq2, hm2⟩
                dsimp only at hq''lo hq''le hsq2 ⊢
                refine hJ1 (p + 1, q'', rem'', ()) mJ1 ⟨wstk2, hq''lo,
                  by rw [hp1_eq]; exact hq''le,
                  by rw [hp1_eq]; omega,
                  by rw [hp1_eq]; exact Nat.lt_succ_self p.toNat, hwl2,
                  fun idx hidx => hr2 idx (by rw [hp1_eq] at hidx; exact hidx),
                  fun F_cur hw => ⟨hsq2 F_cur hw, by
                    rw [hp1_eq, show end_ - (p.toNat + 1) = (end_ - p.toNat) - 1 by omega]
                    exact modeWatchSlice_bin_tail' (hsl1 F_cur hw).2 hrem_pos hw0_eq
                      (by rw [← hw0_val]; assumption)⟩, hm2⟩)
              (fun J2 hJ2 => by
                refine wp_join_group (fun () mJ2 => mJ2 = ml)
                  (by
                    rintro _ _ mJ2 rfl
                    fbl_group
                    have hq1 : (q + 1).toNat = q.toNat + 1 := by bv_omega
                    let wstk2 := wstk1.set q.toNat (wstk1[p.toNat]'(by omega))
                    refine hJ2 (q + 1, rem, ()) _ ⟨wstk2, by rw [hq1]; omega,
                      by rw [hq1]; omega, by rw [List.length_set, hwl1],
                      fun idx hidx => ?_, fun F_cur hw => ?_, by assumption⟩
                    · rw [List.getElem?_set_ne (by rcases hidx with h | h <;> omega)]
                      exact hrest1 idx
                        (by rcases hidx with h | h; exact Or.inl h; exact Or.inr (by omega))
                    · rw [hq1]
                      refine modeWatchSlice_copy_bin (wstk' := wstk2) hq_lo hrem_pos hw0_eq
                        (by rw [← hw0_val]; assumption)
                        (fun idx hidx => ?_) ?_ (hsl1 F_cur hw).1 (hsl1 F_cur hw).2
                      · rw [List.getElem?_set_ne (by omega)]
                      · rw [List.getElem?_eq_getElem (by rw [List.length_set]; omega),
                          List.getElem_set_self, hw0_val])
                  (fun J3 hJ3 => by
                    fbl_group
                    · exact hJ3 () ml rfl
                    · refine hJ2 (q, true, ()) _ ⟨wstk1, hq_lo, by omega, hwl1,
                        fun idx hidx => hrest1 idx
                          (by rcases hidx with h | h; exact Or.inl h; exact Or.inr (by omega)),
                        fun F_cur hw => (hsl1 F_cur hw).1, hm1⟩
                    · exact hJ3 () ml rfl))
          · -- large clause branch
            have h2le : 2 ≤ end_ - p.toNat :=
              (modeWatchSlice_large_tail' (hsl1 F_base hw_base).2 hrem_pos hw0_eq
                (by rw [← hw0_val]; assumption)).1
            have hp1_lt_end : (p + 1).toNat < end_ := by omega
            have hcr_val : wstk1[p.toNat + 1]'(by omega) =
                s.core.wstk[p.toNat + 1]'(by omega) := by
              have := hrest1 (p.toNat + 1) (Or.inr (by omega))
              rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at this
              exact Option.some.inj this
            have hcr_eq : s.core.wstk[p.toNat + 1]? =
                some (s.core.wstk[p.toNat + 1]'(by omega)) :=
              List.getElem?_eq_getElem (by omega)
            refine wp_join_group
              (fun (p'', q'', ()) mJ1 => ∃ wstk2 : List (BitVec 32),
                off ≤ q''.toNat ∧ q''.toNat ≤ p''.toNat ∧ p''.toNat ≤ end_ ∧ p.toNat < p''.toNat ∧
                wstk2.length = c.wcap ∧
                (∀ idx, idx < off ∨ p''.toNat ≤ idx → wstk2[idx]? = s.core.wstk[idx]?) ∧
                (∀ F_cur, FullWitnessInv c F0 F_cur s.core →
                  (if s.core.dense_mode = 0#64 then
                     WatchSliceOk F_cur { s.core with wstk := wstk2 } lit.toNat off
                       (q''.toNat - off)
                   else
                     DenseWatchSliceOk F_cur { s.core with wstk := wstk2 } lit.toNat off
                       (q''.toNat - off)) ∧
                  (if s.core.dense_mode = 0#64 then
                     WatchSliceOk F_cur s.core lit.toNat p''.toNat (end_ - p''.toNat)
                   else
                     DenseWatchSliceOk F_cur s.core lit.toNat p''.toNat (end_ - p''.toNat))) ∧
                (FullMem c { s with core := { s.core with wstk := wstk2 } } ⋆ R) mJ1)
              (by
                rintro _ ⟨p'', q'', ⟨⟩⟩ mJ1
                  ⟨wstk2, hq''lo, hq''p'', hp''hi, hpgt, hwl2, hr2, hs2, hm2⟩
                dsimp only at hq''lo hq''p'' hp''hi hpgt hr2 hs2 ⊢
                exact hJ1 _ mJ1 ⟨wstk2, hq''lo, hq''p'', hp''hi, hpgt, hwl2, hr2, hs2, hm2⟩)
              (fun J2 hJ2 => by
                fbl_group
                · have hp2_eq : (p + 1 + 1).toNat = p.toNat + 2 := by bv_omega
                  have hq2_eq : (q + 2).toNat = q.toNat + 2 := by bv_omega
                  let wstk2 := (wstk1.set q.toNat (wstk1[p.toNat]'(by omega))).set
                    (q.toNat + 1) (wstk1[p.toNat + 1]'(by omega))
                  refine hJ2 (p + 1 + 1, q + 2, ()) _ ⟨wstk2, by rw [hq2_eq]; omega,
                    by rw [hp2_eq, hq2_eq]; omega, by rw [hp2_eq]; omega, by rw [hp2_eq]; omega,
                    by rw [List.length_set, List.length_set, hwl1],
                    fun idx hidx => ?_, fun F_cur hw => ⟨?_, ?_⟩, ?_⟩
                  · rw [hp2_eq] at hidx
                    rw [List.getElem?_set_ne (by rcases hidx with h | h <;> omega),
                        List.getElem?_set_ne (by rcases hidx with h | h <;> omega)]
                    exact hrest1 idx
                      (by rcases hidx with h | h; exact Or.inl h; exact Or.inr (by omega))
                  · rw [hq2_eq]
                    refine modeWatchSlice_copy_large (wstk' := wstk2) hq_lo hrem_pos hw0_eq hcr_eq
                      (by rw [← hw0_val]; assumption)
                      (fun idx hidx => ?_) ?_ ?_ (hsl1 F_cur hw).1 (hsl1 F_cur hw).2
                    · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
                    · rw [List.getElem?_set_ne (by omega),
                        List.getElem?_eq_getElem (by rw [List.length_set]; omega),
                        List.getElem_set_self, hw0_val]
                    · rw [List.getElem?_eq_getElem
                          (by rw [List.length_set, List.length_set]; omega),
                        List.getElem_set_self, hcr_val]
                  · rw [hp2_eq, show end_ - (p.toNat + 2) = (end_ - p.toNat) - 2 by omega]
                    exact (modeWatchSlice_large_tail' (hsl1 F_cur hw).2 hrem_pos hw0_eq
                      (by rw [← hw0_val]; assumption)).2
                  · simp only [wstk2, ← hp1_eq, ← show (q + 1).toNat = q.toNat + 1 by bv_omega]
                    assumption))
    · -- Loop 1 exit: `!(p < end)`, so `p.toNat = end_`
      have hp_end : p.toNat = end_ := by
        have hnot : ¬ p.toNat < end_ := by rw [← h_cond_lt]; assumption
        omega
      have hsl_q : ∀ F_cur, FullWitnessInv c F0 F_cur s.core →
          if s.core.dense_mode = 0#64 then
            WatchSliceOk F_cur { s.core with wstk := wstk1 } lit.toNat off (q.toNat - off)
          else
            DenseWatchSliceOk F_cur { s.core with wstk := wstk1 } lit.toNat off (q.toNat - off) :=
        fun F_cur hw => (hsl1 F_cur hw).1
      have hrest_out : ∀ idx, idx < off ∨ end_ ≤ idx → wstk1[idx]? = s.core.wstk[idx]? := by
        intro idx hidx; exact hrest1 idx (by rw [hp_end]; exact hidx)
      refine wp_loop_inv
        (fun (k, ()) ml2 => ∃ wstk2 : List (BitVec 32),
          q.toNat ≤ k.toNat ∧ k.toNat ≤ end_ ∧ wstk2.length = c.wcap ∧
          (∀ idx < q.toNat - off, wstk2[off + idx]? = wstk1[off + idx]?) ∧
          (∀ idx, idx < off ∨ end_ ≤ idx → wstk2[idx]? = s.core.wstk[idx]?) ∧
          (FullMem c { s with core := { s.core with wstk := wstk2 } } ⋆ R) ml2)
        (fun (k, ()) _ => end_ - k.toNat)
        (fun J2 hJ2 => hJ2 (q, ()) ml ⟨wstk1, le_refl _, by omega, hwl1, fun _ _ => rfl,
          hrest_out, hm1⟩)
        (fun J2 (k, ()) ml2 ⟨wstk2, hqk, hk_hi, hwl2, hpref2, hout2, hm2⟩ ih2 => ?_)
      fbl_group
      · have hk_lt : k.toNat < end_ := by rw [← h_cond_lt]; assumption
        have hk1_eq : (k + 1).toNat = k.toNat + 1 := by bv_omega
        let wstk3 := wstk2.set k.toNat 0xFFFFFFFF#32
        refine ih2 (k + 1, ()) _ (by dsimp only; omega)
          ⟨wstk3, by rw [hk1_eq]; omega, by rw [hk1_eq]; omega,
          by rw [List.length_set, hwl2], fun idx hidx => ?_, fun idx hidx => ?_, by assumption⟩
        · rw [List.getElem?_set_ne (by omega)]; exact hpref2 idx hidx
        · rw [List.getElem?_set_ne (by rcases hidx with h | h <;> omega)]; exact hout2 idx hidx
      · have hk_end : k.toNat = end_ := by
          have hnot : ¬ k.toNat < end_ := by rw [← h_cond_lt]; assumption
          omega
        have hidx0' : (lit.setWidth 64 <<< (1 : Nat)).toNat = 2 * lit.toNat := by bv_omega
        have hidx1' : (lit.setWidth 64 <<< (1 : Nat) + (1 : BitVec 64)).toNat =
            2 * lit.toNat + 1 := by bv_omega
        have hq_sub_lt : q.toNat - off < 2 ^ 32 := by omega
        have hq_trunc : (BitVec.setWidth 32 (q -
            BitVec.setWidth 64 (s.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'(by
              rw [hidx0']; omega)))).toNat =
            q.toNat - off := by
          simp only [BitVec.toNat_setWidth, BitVec.toNat_sub]
          have := h_off; rw [Nat.mod_eq_of_lt] <;> bv_omega
        let wvec' := s.core.wvec.set (lit.setWidth 64 <<< (1 : Nat) + (1 : BitVec 64)).toNat
          (BitVec.setWidth 32 (q -
            BitVec.setWidth 64 (s.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'(by
              rw [hidx0']; omega))))
        let wu' := s.core.wusable +
          (BitVec.setWidth 64 (s.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'(by
              rw [hidx0']; omega)) +
            BitVec.setWidth 64 (s.core.wvec[(lit.setWidth 64 <<< (1 : Nat) +
              (1 : BitVec 64)).toNat]'(by rw [hidx1']; omega)) - q)
        let s' : FullState :=
          { s with core := { s.core with wvec := wvec', wstk := wstk2, wusable := wu' } }
        have hlen' : s'.LengthsOk c :=
          ⟨{ hcl with wvec_len := by simp [s', wvec', hwvl], wstk_len_arr := hwl2 },
           hinv.lengths.scratch_ok⟩
        refine hQ wvec' wstk2 wu' _ hlen' (fun F_cur hw => ?_) (by assumption)
        have hwvec_self : fullWatchOffCore s'.core lit.toNat = off ∧
            fullWatchSizeCore s'.core lit.toNat = q.toNat - off := by
          constructor
          · unfold fullWatchOffCore; simp only [s', wvec']
            rw [List.getElem?_set_ne (by rw [hidx1']; omega)]; rfl
          · unfold fullWatchSizeCore; simp only [s', wvec']
            rw [hidx1', List.getElem?_eq_getElem (by rw [List.length_set]; omega),
              List.getElem_set_self, Option.getD_some, hq_trunc]
        have hwvec_other : ∀ l < 2 * s.core.cur_vars, l ≠ lit.toNat →
            fullWatchOffCore s'.core l = fullWatchOffCore s.core l ∧
            fullWatchSizeCore s'.core l = fullWatchSizeCore s.core l := by
          intro l _ hne; unfold fullWatchOffCore fullWatchSizeCore; simp only [s', wvec']
          rw [List.getElem?_set_ne (by rw [hidx1']; omega),
              List.getElem?_set_ne (by rw [hidx1']; omega)]
          exact ⟨rfl, rfl⟩
        have hslice_new : if s.core.dense_mode = 0#64 then
            WatchSliceOk F_cur s'.core lit.toNat off (q.toNat - off)
          else DenseWatchSliceOk F_cur s'.core lit.toNat off (q.toNat - off) :=
          modeWatchSlice_relocate (k := { s.core with wstk := wstk1 }) (k' := s'.core)
            (p := off) (p' := off) (Nat.le_refl _) rfl (fun _ r => r) hpref2 (hsl_q F_cur hw)
        have hwat' : ModeWatchesInv F_cur s'.core :=
          fbl_compactSlice_preserves_modeWatches hw.watches rfl rfl rfl (fun _ r => r) hlit_lt
            hq_lo (by omega) hwvec_self hwvec_other hout2 hslice_new
        exact { hw with
          arena := { hw.arena with len_ok := hw.arena.len_ok }
          watches := hwat' }

theorem full_delete_binary_wp (Γ : Env)
    (hdbs : EnvSpec Γ "full_delete_bin_side" fullDeleteBinSideSpec) :
    ∀ args m Q X, fullDeleteBinarySpec args m Q X →
      Func.wp Γ full_delete_binary_body args m Q X := by
  rintro ⟨h, a, b, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩
  fbl_group
  c0_call hdbs
  refine ⟨c, F0, s, R, rfl, hinv, hm, ?_⟩
  dsimp only
  intro wvec1 wstk1 wu1 m1 hlen1 htr1 hm1
  let s1 : FullState :=
    { s with core := { s.core with wvec := wvec1, wstk := wstk1, wusable := wu1 } }
  have hinv1 : FullCoreInv c F0 s1 := by
    obtain ⟨F_base, hw_base⟩ := hinv.witness
    exact ⟨hlen1, F_base, htr1 F_base hw_base⟩
  c0_call hdbs
  refine ⟨c, F0, s1, R, rfl, hinv1, hm1, ?_⟩
  dsimp only
  intro wvec2 wstk2 wu2 m2 hlen2 htr2 hm2
  refine wp_join_group
    (fun _ mJ => ∃ nb',
      let s' : FullState :=
        { s with core := { s.core with wvec := wvec2, wstk := wstk2,
                                       wusable := wu2, num_binary := nb' } }
      s'.LengthsOk c ∧
      (∀ F_cur, FullWitnessInv c F0 F_cur s.core → FullWitnessInv c F0 F_cur s'.core) ∧
      (FullMem c s' ⋆ R) mJ)
    (by
      rintro _ _ mJ ⟨nb', hlen', htr', hm'⟩
      exact hQ wvec2 wstk2 wu2 nb' mJ hlen' htr' hm')
    (fun J hJ => by
      fbl_group
      · refine hJ () _ ⟨s.core.num_binary - 1#64, ⟨{ hlen2.core_ok with }, hlen2.scratch_ok⟩,
          fun F_cur hw => ?_, by assumption⟩
        have hw2 := htr2 F_cur (htr1 F_cur hw)
        exact { hw2 with
          arena := { hw2.arena with len_ok := hw2.arena.len_ok }
          watches := hw2.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }
      · exact hJ () m2 ⟨s.core.num_binary, hlen2, fun F_cur hw => htr2 F_cur (htr1 F_cur hw),
          hm2⟩)

end LeanQbe.T.Examples.Kissat.Full
