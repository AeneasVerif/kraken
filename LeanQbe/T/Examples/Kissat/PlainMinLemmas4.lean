module

public import LeanQbe.T.Examples.Kissat.PlainMinLemmas3

/-!
# Soundness Proofs for Kissat `D-Plain` Block Shrink (Part 4)

Proves the parametric `(Γ : Env)` `Func.wp` contract for `plain_shrink_blk`
(`plainShrinkBlkSpec`, `plain_shrink_blk_wp`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Plain

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

open scoped PlainMinTactics

private def shrinkBlkAfterExpr (hdr beg end_b pTmp pMark pShrinkStk : Val i64)
    (xs : Tup Val [i64, i64, .bool, i32, i64]) : Expr Val Cont [] :=
  let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg Val i64) : Op Val [i64] :=
    Op.mk c (a, b, ())
  .group (sig := [[]]) (fun _ => .cons (fun _ =>
    shrinkBlkClearExpr pMark pShrinkStk xs.snd.fst) .nil)
    fun Js => .jnz (.var xs.snd.snd.fst) (.jump Js.fst ())
      (.let_ (Op.mk (.cmp .eq i32 .bool rfl)
          (.var xs.snd.snd.snd.fst, .imm 4294967295, ())) fun p_12 =>
       .jnz (.var p_12.fst) (.jump Js.fst ())
         (.let_ (Op.mk (.xor i32) (.var xs.snd.snd.snd.fst, .imm 1, ())) fun p_13 =>
          .group (sig := [[i64]]) (fun Js => .cons (fun p_14 =>
            .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var p_14.fst, .var end_b, ())) fun p_15 =>
            .jnz (.var p_15.fst)
              (.let_ (op64 (.mul i64) (.var p_14.fst) (.imm 4)) fun p =>
               .let_ (op64 (.add i64) (.var pTmp) (.var p.fst)) fun p =>
               .store (t := i32) (.imm 4294967295) (.var p.fst)
                 (.let_ (op64 (.add i64) (.var p_14.fst) (.imm 1)) fun p =>
                  .jump Js.fst (.var p.fst, ())))
              (.let_ (op64 (.mul i64) (.var beg) (.imm 4)) fun p_16 =>
               .let_ (op64 (.add i64) (.var pTmp) (.var p_16.fst)) fun p_17 =>
               .store (.var p_13.fst) (.var p_17.fst)
                 (.group (sig := [[i64]]) (fun Js => .cons (fun p_18 =>
                   .let_ (Op.mk (.cmp .ult i64 .bool rfl)
                       (.var p_18.fst, .var xs.snd.fst, ())) fun p_19 =>
                   .jnz (.var p_19.fst)
                     (.let_ (op64 (.mul i64) (.var p_18.fst) (.imm 4)) fun p_20 =>
                      .let_ (op64 (.add i64) (.var pShrinkStk) (.var p_20.fst)) fun p_21 =>
                      .load i32 (.var p_21.fst) fun ld =>
                      .let_ (Op.mk (.zext 32 64) (.var ld, ())) fun p_22 =>
                      .let_ (op64 (.add i64) (.var pMark) (.var p_22.fst)) fun p_23 =>
                      .let_ (Op.mk (.zext 32 64) (.var ld, ())) fun p_24 =>
                      .let_ (op64 (.add i64) (.var pMark) (.var p_24.fst)) fun p_25 =>
                      .load i8 (.var p_25.fst) fun ld_8 =>
                      .let_ (Op.mk (.trunc 32 8) (.imm 247, ())) fun p_26 =>
                      .let_ (Op.mk (.zext 8 32) (.var ld_8, ())) fun p_27 =>
                      .let_ (Op.mk (.zext 8 32) (.var p_26.fst, ())) fun p_28 =>
                      .let_ (Op.mk (.and i32) (.var p_27.fst, .var p_28.fst, ())) fun p_29 =>
                      .let_ (Op.mk (.trunc 32 8) (.var p_29.fst, ())) fun p_30 =>
                      .store (.var p_30.fst) (.var p_23.fst)
                        (.let_ (Op.mk (.trunc 32 8) (.imm 2, ())) fun p_31 =>
                         .call "plain_min_mark" (as := [i64, i32, i8]) (bs := [])
                           (.var hdr, .var ld, .var p_31.fst, ()) fun _ =>
                         .let_ (op64 (.add i64) (.var p_18.fst) (.imm 1)) fun p =>
                         .jump Js.fst (.var p.fst, ())))
                     (.ret ())) .nil)
                   (fun Js => .jump Js.fst (.imm 0, ()))))) .nil)
            fun Js => .jump Js.fst (.var beg, ())))

private theorem shrink_blk_after_wp {Γ : Env}
    (hMm : ∀ args m Q X, plainMinMarkSpec args m Q X →
      Γ "plain_min_mark" [i64, i32, i8] [] args m Q X)
    {c : PlainCfg} {F0 : CNF Nat} {s : PlainState} {beg end_b : Val i64} {blvl : Val i32}
    {R : Mem 64 → Prop} {Q : Post []} {X : XPost}
    (hcore : PlainCoreInv c F0 s) (hbeg1 : 1 ≤ beg.toNat) (hbeg_end : beg.toNat < end_b.toNat)
    (hend_tl : end_b.toNat ≤ s.tmp_len) (htl_mv : s.tmp_len ≤ c.mv)
    (hEnt0 : F0.EntailsClause (cnfClause
      (((s.tmp.take s.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat)))
    (hblk_spec : ∀ k, beg.toNat ≤ k → k < end_b.toNat →
      (s.lvl[(s.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = blvl.toNat)
    (hkeep_spec : ∀ k < s.tmp_len, s.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
      let l := (s.tmp[k]?.getD 0#32).toNat
      l < 2 * c.mv ∧ s.vals[l]?.getD 0#8 = 0xFF#8 ∧ (s.mrk[l / 2]?.getD 0#8 &&& 2#8) ≠ 0#8)
    (hQ : ∀ tmp' mrk' mstk' mclr' mcl' mcf' heur' m',
      let s' : PlainState :=
        { s with tmp := tmp', mrk := mrk', min_stk := mstk', min_clr := mclr',
                 min_clr_len := mcl', min_clr_full := mcf', heur := heur' }
      PlainCoreInv c F0 s' → PlainMinMarkInv c F0 s'
        (((tmp'.take s.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat) →
      (∀ v < c.mv, (mrk'[v]?.getD 0#8 &&& 8#8) = 0#8) → tmp'.length = c.mv →
      heur'.rel_trigger = s.heur.rel_trigger →
      (∀ v < c.mv, (s.mrk[v]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk'[v]?.getD 0#8 &&& 2#8) ≠ 0#8) →
      (∀ k < s.tmp_len, (k < beg.toNat ∨ end_b.toNat ≤ k) → tmp'[k]? = s.tmp[k]?) →
      (∀ k, beg.toNat ≤ k → k < end_b.toNat → tmp'[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
        (s.lvl[(tmp'[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = blvl.toNat) →
      F0.EntailsClause (cnfClause
        (((tmp'.take s.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat)) →
      (∀ k < s.tmp_len, tmp'[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
        let l := (tmp'[k]?.getD 0#32).toNat
        l < 2 * c.mv ∧ s'.vals[l]?.getD 0#8 = 0xFF#8 ∧ (mrk'[l / 2]?.getD 0#8 &&& 2#8) ≠ 0#8) →
      (PlainMem c s' ⋆ R) m' → Q () m')
    {xs : Tup Val [i64, i64, .bool, i32, i64]} {m_a : Mem 64}
    (ha : ShrinkAfterInv c F0 s blvl beg.toNat end_b.toNat
      (((s.tmp.take s.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat) R xs m_a) :
    wp Γ Q X (shrinkBlkAfterExpr c.hdr beg end_b c.pTmp c.pMark c.pShrinkStk xs) m_a := by
  dsimp only [shrinkBlkAfterExpr]
  rcases xs with ⟨open_a, slen_a, failed_a, uip_a, t_a, ⟨⟩⟩
  rcases ha with ⟨mrk_a, mstk_a, mclr_a, sstk_a, mcl_a, mcf_a, hb_a, hsstk_a, hm_a, hsucc_a⟩
  have hmv := c.hmv; unfold dimacsBound at hmv; have hlen0 := hcore.lengths
  refine wp_join_group (ts := []) (fun () m_f => m_f = m_a) ?_ ?_
  · rintro J_fl ⟨⟩ m_f hm_f_eq; subst m_f; rw [Blocks.get_here]
    exact shrink_blk_clear_wp hcore hb_a hm_a fun mrk_f m_f hcore_f hmin_f hno8_f hmono_f hm_f =>
      hQ s.tmp mrk_f mstk_a mclr_a mcl_a mcf_a { s.heur with shrink_stk := sstk_a } m_f hcore_f
        hmin_f hno8_f hlen0.tmp_len_arr rfl hmono_f (fun _ _ _ => rfl)
        (fun k hk1 hk2 _ => hblk_spec k hk1 hk2) hEnt0
        (fun k hk hne => let sp := hkeep_spec k hk hne; ⟨sp.1, sp.2.1, hmono_f _ (by omega) sp.2.2⟩)
        hm_f
  · rintro J_fl hJ_fl
    ml_jnz; refine ⟨fun _ => ?_, fun hnfail => ?_⟩
    · ml_lets; exact hJ_fl () m_a rfl
    · ml_lets; ml_jnz; refine ⟨fun _ => ?_, fun huip_ne => ?_⟩
      · ml_lets; exact hJ_fl () m_a rfl
      · c0_cond huip_ne
        obtain ⟨idx_uip, huip_te, huip_eq, huip_8, huip_lvl, hblk_a, hres_a⟩ :=
          hsucc_a hnfail huip_ne
        ml_lets
        refine wp_loop_group (ts := [i64]) (fun n (k_bv, ()) m_k =>
            ∃ (tmp_k : List (BitVec 32)),
              n = end_b.toNat - k_bv.toNat ∧ beg.toNat ≤ k_bv.toNat ∧ k_bv.toNat ≤ end_b.toNat ∧
              tmp_k.length = c.mv ∧
              (∀ j < s.tmp_len, (j < beg.toNat ∨ k_bv.toNat ≤ j) → tmp_k[j]? = s.tmp[j]?) ∧
              (∀ j, beg.toNat ≤ j → j < k_bv.toNat → tmp_k[j]? = some 0xFFFFFFFF#32) ∧
              (PlainMem c (shrinkBlkSt s tmp_k mrk_a mstk_a mclr_a mcl_a mcf_a sstk_a) ⋆ R) m_k)
          ?_ ?_
        · rintro Jk n ⟨k_bv, ⟨⟩⟩ m_k hJk ⟨tmp_k, rfl, hbk, hke, htk_len, htk_out, htk_set, hm_k⟩
          rw [Blocks.get_here]; ml_lets; ml_jnz; refine ⟨fun hklt => ?_, fun hkge => ?_⟩
          · c0_cond hklt
            have hkt : k_bv.toNat < (shrinkBlkSt s tmp_k mrk_a mstk_a mclr_a mcl_a mcf_a
                sstk_a).tmp.length := by dsimp only [shrinkBlkSt]; rw [htk_len]; omega
            ml_st m_k2, hm_s := c0_store_arena_tmp (s := shrinkBlkSt s tmp_k mrk_a mstk_a
              mclr_a mcl_a mcf_a sstk_a) (i := k_bv) 0xFFFFFFFF#32 hkt hm_k
            ml_lets
            let tmp_k2 := tmp_k.set k_bv.toNat 0xFFFFFFFF#32
            have hk1 : (k_bv + 1).toNat = k_bv.toNat + 1 := min_bv64_add1 (by omega)
            refine hJk (end_b.toNat - (k_bv + 1).toNat) (k_bv + 1, ()) m_k2 (by omega)
              ⟨tmp_k2, rfl, by rw [hk1]; omega, by rw [hk1]; omega, by simp [tmp_k2, htk_len],
                fun j hj hjb => ?_, fun j hj1 hj2 => ?_, by
                  dsimp only [shrinkBlkSt, tmp_k2] at hm_s ⊢; exact hm_s⟩
            · rw [hk1] at hjb
              by_cases hjk : j = k_bv.toNat
              · omega
              · dsimp only [tmp_k2]; rw [List.getElem?_set_ne (Ne.symm hjk)]
                exact htk_out j hj (hjb.elim Or.inl fun h => Or.inr (by omega))
            · rw [hk1] at hj2; dsimp only [tmp_k2]; by_cases hjk : j = k_bv.toNat
              · subst j; rw [List.getElem?_set_self (by rw [htk_len]; omega)]
              · rw [List.getElem?_set_ne (Ne.symm hjk)]; exact htk_set j hj1 (by omega)
          · ml_lets; c0_cond hkge
            have hkb_end : k_bv = end_b := BitVec.eq_of_toNat_eq (by omega)
            subst k_bv
            have hbt : beg.toNat < (shrinkBlkSt s tmp_k mrk_a mstk_a mclr_a mcl_a mcf_a
                sstk_a).tmp.length := by dsimp only [shrinkBlkSt]; rw [htk_len]; omega
            ml_st m_sf, hm_sf := c0_store_arena_tmp (s := shrinkBlkSt s tmp_k mrk_a mstk_a
              mclr_a mcl_a mcf_a sstk_a) (i := beg) (uip_a ^^^ 1#32) hbt hm_k
            let tmp_f := tmp_k.set beg.toNat (uip_a ^^^ 1#32)
            have htf_len : tmp_f.length = c.mv := by simp [tmp_f, htk_len]
            have htf_out : ∀ k < s.tmp_len, (k < beg.toNat ∨ end_b.toNat ≤ k) →
                tmp_f[k]? = s.tmp[k]? := fun k hk hkb => by
              dsimp only [tmp_f]; rw [List.getElem?_set_ne (by omega)]; exact htk_out k hk hkb
            have htf_beg : tmp_f[beg.toNat]? = some (uip_a ^^^ 1#32) := by
              dsimp only [tmp_f]; rw [List.getElem?_set_self (by rw [htk_len]; omega)]
            have htf_rest : ∀ k, beg.toNat < k → k < end_b.toNat →
                tmp_f[k]? = some 0xFFFFFFFF#32 := fun k hk1 hk2 => by
              dsimp only [tmp_f]; rw [List.getElem?_set_ne (by omega)]
              exact htk_set k (by omega) hk2
            ml_lets
            refine wp_loop_group (ts := [i64]) (fun n (i_bv, ()) m_i =>
                ∃ (mrk_i : List (BitVec 8)) (mclr_i : List (BitVec 32)) (mcl_i : Nat)
                  (mcf_i : BitVec 64),
                  n = slen_a.toNat - i_bv.toNat ∧ i_bv.toNat ≤ slen_a.toNat ∧
                  mrk_i.length = c.mv ∧ mclr_i.length = c.mv ∧ mcl_i ≤ c.mv ∧
                  (∀ w < c.mv, (mrk_i[w]?.getD 0#8 &&& 0xF1#8) = 0#8) ∧
                  (mcf_i = 0#64 → ∀ w < c.mv, (mrk_i[w]?.getD 0#8 &&& 6#8) ≠ 0#8 →
                    ∃ k < mcl_i, (mclr_i[k]?.getD 0#32).toNat = w) ∧
                  (∀ w < c.mv, (mrk_a[w]?.getD 0#8 &&& 2#8) ≠ 0#8 →
                    (mrk_i[w]?.getD 0#8 &&& 2#8) ≠ 0#8) ∧
                  (∀ j < slen_a.toNat, j < i_bv.toNat →
                    (mrk_i[(sstk_a[j]?.getD 0#32).toNat]?.getD 0#8 &&& 2#8) ≠ 0#8) ∧
                  (∀ w < c.mv, (mrk_i[w]?.getD 0#8 &&& 2#8) ≠ 0#8 →
                    (mrk_a[w]?.getD 0#8 &&& 2#8) ≠ 0#8 ∨ (mrk_a[w]?.getD 0#8 &&& 8#8) ≠ 0#8) ∧
                  (∀ w < c.mv, (mrk_i[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
                    ∃ j, i_bv.toNat ≤ j ∧ j < slen_a.toNat ∧ (sstk_a[j]?.getD 0#32).toNat = w) ∧
                  (PlainMem c (shrinkBlkSt s tmp_f mrk_i mstk_a mclr_i mcl_i mcf_i
                    sstk_a) ⋆ R) m_i) ?_ ?_
            · rintro Ji n ⟨i_bv, ⟨⟩⟩ m_i hJi ⟨mrk_i, mclr_i, mcl_i, mcf_i, rfl, hilen,
                hmri_len, hmclri_len, hmcli_le, hdom_i, hcov_i, hmono_i, h2_sstk, hnew2_i,
                h8_i, hm_i⟩
              rw [Blocks.get_here]; ml_lets; ml_jnz; refine ⟨fun hilt => ?_, fun hidone => ?_⟩
              · c0_cond hilt
                have hi_stk : i_bv.toNat < (shrinkBlkSt s tmp_f mrk_i mstk_a mclr_i mcl_i
                    mcf_i sstk_a).heur.shrink_stk.length := by
                  dsimp only [shrinkBlkSt]; rw [hb_a.sstk_len]
                  exact lt_of_lt_of_le hilt hb_a.slen_le
                have hi_stk' : i_bv.toNat < sstk_a.length := by
                  dsimp only [shrinkBlkSt] at hi_stk; exact hi_stk
                ml_ld c0_load_arena_shrink_stk (s := shrinkBlkSt s tmp_f mrk_i mstk_a mclr_i
                  mcl_i mcf_i sstk_a) (i := i_bv) hi_stk hm_i
                let sv := sstk_a[i_bv.toNat]'hi_stk
                have hsv_lt : sv.toNat < c.mv := by
                  have := hb_a.sstk_lt i_bv.toNat hilt
                  rwa [List.getElem?_eq_getElem hi_stk', Option.getD_some] at this
                have hsv64 : (sv.setWidth 64).toNat = sv.toNat := bv_c0_zext32_64 sv
                ml_ld c0_load_arena_mrk (s := shrinkBlkSt s tmp_f mrk_i mstk_a mclr_i mcl_i
                  mcf_i sstk_a) (i := sv.setWidth 64)
                  (by dsimp only [shrinkBlkSt]; rw [hmri_len, hsv64]; exact hsv_lt) hm_i
                ml_st m_i2, hm_s := c0_store_arena_mrk (s := shrinkBlkSt s tmp_f mrk_i mstk_a
                  mclr_i mcl_i mcf_i sstk_a) (i := sv.setWidth 64) _
                  (by dsimp only [shrinkBlkSt]; rw [hmri_len, hsv64]; exact hsv_lt) hm_i
                let mrk_i2 := mrk_i.set sv.toNat (mrk_i[sv.toNat]?.getD 0#8 &&& 0xF7#8)
                have hm_s' := hm_s
                dsimp only [shrinkBlkSt, sv] at hm_s'
                simp only [bv_c0_zext32_64, Arg.val_var, bv8_and247_c0] at hm_s'
                have hm_i2 : (PlainMem c (shrinkBlkSt s tmp_f mrk_i2 mstk_a mclr_i mcl_i
                    mcf_i sstk_a) ⋆ R) m_i2 := by
                  dsimp only [shrinkBlkSt, mrk_i2, sv]
                  rw [List.getElem?_eq_getElem (by rw [hmri_len]; exact hsv_lt), Option.getD_some]
                  exact hm_s'
                let sb_i2 := shrinkBlkSt s tmp_f mrk_i2 mstk_a mclr_i mcl_i mcf_i sstk_a
                have hln_i2 : sb_i2.LengthsOk c :=
                  (coreInv_shrinkBlk hcore (mcf1 := mcf_i) htf_len
                    (by simp [mrk_i2, hmri_len]) hb_a.mstk_len hmclri_len hmcli_le
                    hb_a.sstk_len).lengths
                have hno8_sv : (sb_i2.mrk[sv.toNat]?.getD 0#8 &&& 8#8) = 0#8 := by
                  dsimp only [sb_i2, shrinkBlkSt, mrk_i2]
                  rw [List.getElem?_set_self (by rw [hmri_len]; exact hsv_lt), Option.getD_some]
                  exact bv8_and8_clear _
                ml_lets; apply wp_call_of_spec; apply hMm
                refine plainMinMarkSpec_step hln_i2 hm_i2 sv hsv_lt
                  ((2 : BitVec 32).setWidth 8) fun m_m hm_m => ?_
                have h2_eq : (2 : BitVec 32).setWidth 8 = 2#8 := rfl
                rw [h2_eq] at hm_m
                let sb_i3 := plainMinMarkStepState c sb_i2 sv.toNat 2#8
                have hln_i3 := plainMinMarkStepState_lengths hln_i2 sv.toNat 2#8
                have hdom_i2 : ∀ w < c.mv, (sb_i2.mrk[w]?.getD 0#8 &&& 0xF1#8) = 0#8 := by
                  intro w hw; dsimp only [sb_i2, shrinkBlkSt, mrk_i2]
                  by_cases hwe : w = sv.toNat
                  · subst w; rw [List.getElem?_set_self (by rw [hmri_len]; exact hsv_lt),
                      Option.getD_some]
                    exact bv8_and_dom_clear8 (hdom_i _ hsv_lt)
                  · rw [List.getElem?_set_ne (Ne.symm hwe)]; exact hdom_i w hw
                have hcov_i2 : sb_i2.min_clr_full = 0#64 → ∀ w < c.mv,
                    (sb_i2.mrk[w]?.getD 0#8 &&& 6#8) ≠ 0#8 →
                    ∃ k < sb_i2.min_clr_len, (sb_i2.min_clr[k]?.getD 0#32).toNat = w := by
                  intro hmcf w hw h6; dsimp only [sb_i2, shrinkBlkSt, mrk_i2] at hmcf h6 ⊢
                  by_cases hwe : w = sv.toNat
                  · subst w; rw [List.getElem?_set_self (by rw [hmri_len]; exact hsv_lt),
                      Option.getD_some, bv8_and6_pres_clear8] at h6
                    exact hcov_i hmcf _ hsv_lt h6
                  · rw [List.getElem?_set_ne (Ne.symm hwe)] at h6; exact hcov_i hmcf w hw h6
                obtain ⟨hdom_i3, hcov_i3⟩ := plainMinMarkStepState_dom_clr hln_i2 hdom_i2
                  hcov_i2 hsv_lt (Or.inl rfl) hno8_sv
                obtain ⟨hbit8_i3, hmono2_i3⟩ := plainMinMarkStepState_bit8_mono2 hln_i2 hsv_lt
                  (Or.inl rfl) hno8_sv
                have hm_i3 : (PlainMem c (shrinkBlkSt s tmp_f sb_i3.mrk mstk_a sb_i3.min_clr
                    sb_i3.min_clr_len sb_i3.min_clr_full sstk_a) ⋆ R) m_m := by
                  dsimp only [sb_i3, sb_i2] at hm_m ⊢; rw [← shrinkBlkSt_step]; exact hm_m
                have hmono_i2 : ∀ w < c.mv, (mrk_i[w]?.getD 0#8 &&& 2#8) ≠ 0#8 →
                    (sb_i2.mrk[w]?.getD 0#8 &&& 2#8) ≠ 0#8 := fun w hw h2 => by
                  dsimp only [sb_i2, shrinkBlkSt, mrk_i2]; by_cases hwe : w = sv.toNat
                  · subst w; rw [List.getElem?_set_self (by rw [hmri_len]; exact hsv_lt),
                      Option.getD_some, bv8_and2_pres_clear8]
                    exact h2
                  · rwa [List.getElem?_set_ne (Ne.symm hwe)]
                have hsv_2 : (sb_i3.mrk[sv.toNat]?.getD 0#8 &&& 2#8) ≠ 0#8 := by
                  dsimp only [sb_i3, plainMinMarkStepState, plainMinMarkState]; split
                  · exact ‹_›
                  · dsimp only
                    rw [List.getElem?_set_self (by rw [hln_i2.mrk_len]; exact hsv_lt),
                      Option.getD_some]
                    exact bv8_and2_of_or2 _
                have hi1 : (i_bv + 1).toNat = i_bv.toNat + 1 :=
                  min_bv64_add1 (by have := hb_a.slen_le; omega)
                ml_lets
                refine hJi (slen_a.toNat - (i_bv + 1).toNat) (i_bv + 1, ()) m_m (by omega)
                  ⟨sb_i3.mrk, sb_i3.min_clr, sb_i3.min_clr_len, sb_i3.min_clr_full,
                    rfl, by omega, hln_i3.mrk_len, hln_i3.min_clr_len_arr,
                    hln_i3.min_clr_len_le, hdom_i3, hcov_i3,
                    fun w hw h2 => hmono2_i3 w hw (hmono_i2 w hw (hmono_i w hw h2)),
                    fun j hj hji1 => ?_, fun w hw h2 => ?_, fun w hw h8 => ?_, hm_i3⟩
                · rw [hi1] at hji1; by_cases hji : j = i_bv.toNat
                  · subst j; dsimp only [sv] at hsv_2
                    rw [List.getElem?_eq_getElem (l := sstk_a) hi_stk', Option.getD_some]
                    exact hsv_2
                  · exact hmono2_i3 _ (hb_a.sstk_lt j hj)
                      (hmono_i2 _ (hb_a.sstk_lt j hj) (h2_sstk j hj (by omega)))
                · by_cases hwe : w = sv.toNat
                  · subst w; right
                    have h1 := hsstk_a i_bv.toNat hilt
                    rw [List.getElem?_eq_getElem (l := sstk_a) hi_stk', Option.getD_some] at h1
                    exact h1
                  · have h2_i2 : (sb_i2.mrk[w]?.getD 0#8 &&& 2#8) ≠ 0#8 := by
                      dsimp only [sb_i3, plainMinMarkStepState, plainMinMarkState] at h2
                      split at h2
                      · exact h2
                      · dsimp only at h2; rwa [List.getElem?_set_ne (Ne.symm hwe)] at h2
                    have h2_i : (mrk_i[w]?.getD 0#8 &&& 2#8) ≠ 0#8 := by
                      dsimp only [sb_i2, shrinkBlkSt, mrk_i2] at h2_i2
                      rwa [List.getElem?_set_ne (Ne.symm hwe)] at h2_i2
                    exact hnew2_i w hw h2_i
                · rw [hi1]; rw [hbit8_i3 w hw] at h8
                  dsimp only [sb_i2, shrinkBlkSt, mrk_i2] at h8
                  by_cases hwe : w = sv.toNat
                  · subst w; rw [List.getElem?_set_self (by rw [hmri_len]; exact hsv_lt),
                      Option.getD_some] at h8
                    exact absurd (bv8_and8_clear _) h8
                  · rw [List.getElem?_set_ne (Ne.symm hwe)] at h8
                    obtain ⟨j, hj1, hj2, hjw⟩ := h8_i w hw h8
                    refine ⟨j, ?_, hj2, hjw⟩
                    by_cases hji : j = i_bv.toNat
                    · subst j; exfalso; apply hwe
                      rw [← hjw, List.getElem?_eq_getElem (l := sstk_a) hi_stk', Option.getD_some]
                      rfl
                    · omega
              · ml_lets; rw [wp]; c0_cond hidone
                have hno8_f : ∀ w < c.mv, (mrk_i[w]?.getD 0#8 &&& 8#8) = 0#8 := fun w hw => by
                  by_cases hnz : (mrk_i[w]?.getD 0#8 &&& 8#8) = 0#8
                  · exact hnz
                  · obtain ⟨j, hj1, hj2, _⟩ := h8_i w hw hnz; omega
                have h8_to_2f : ∀ w < c.mv, (mrk_a[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
                    (mrk_i[w]?.getD 0#8 &&& 2#8) ≠ 0#8 := fun w hw h8 => by
                  obtain ⟨j, hj, hjw⟩ := hb_a.bit8_sstk w hw h8
                  have := h2_sstk j hj (by omega); rwa [hjw] at this
                have hcore_f := coreInv_shrinkBlk hcore (mcf1 := mcf_i) htf_len hmri_len
                  hb_a.mstk_len hmclri_len hmcli_le hb_a.sstk_len
                obtain ⟨hmin_f, hEnt_f, hlvl_f, htmp_f⟩ := shrink_blk_success_finish
                  hcore hbeg1 hbeg_end hend_tl htl_mv hEnt0 hkeep_spec hb_a hmri_len
                  hmclri_len hmcli_le htf_len hdom_i hcov_i hmono_i h8_to_2f hnew2_i
                  huip_te huip_eq huip_8 huip_lvl hres_a hblk_a htf_out htf_beg htf_rest
                dsimp only [shrinkBlkSt] at hmin_f
                exact hQ tmp_f mrk_i mstk_a mclr_i mcl_i mcf_i
                  { s.heur with shrink_stk := sstk_a } m_i hcore_f hmin_f hno8_f
                  htf_len rfl (fun w hw h2 => hmono_i w hw (hb_a.mono2 w hw h2)) htf_out
                  hlvl_f hEnt_f htmp_f hm_i
            · exact fun Ji hJi => by
                ml_lets
                exact hJi slen_a.toNat (0#64, ()) m_sf ⟨mrk_a, mclr_a, mcl_a, mcf_a, rfl,
                  Nat.zero_le _, hb_a.mrk_len, hb_a.mclr_len, hb_a.mcl_le,
                  hb_a.min_inv.mrk_dom, hb_a.min_inv.clr_cov, fun _ _ h => h,
                  fun _ _ h => by simp at h, fun _ _ h => Or.inl h, fun w hw h8 =>
                    let ⟨j, hj, hjw⟩ := hb_a.bit8_sstk w hw h8; ⟨j, Nat.zero_le _, hj, hjw⟩,
                  by dsimp only [shrinkBlkSt, tmp_f] at hm_sf ⊢; exact hm_sf⟩
        · exact fun Jk hJk => by
            ml_lets
            exact hJk (end_b.toNat - beg.toNat) (beg, ()) m_a ⟨s.tmp, rfl, le_refl _,
              le_of_lt hbeg_end, hlen0.tmp_len_arr, fun _ _ _ => rfl, fun _ h1 h2 => by omega, hm_a⟩

/-- `Func.wp` soundness theorem for `plain_shrink_blk` (`PlainSpec.lean:698`). -/
theorem plain_shrink_blk_wp (Γ : Env)
    (hMl : ∀ args m Q X, plainMinLitSpec args m Q X →
      Γ "plain_min_lit" [i64, i32] [.bool] args m Q X)
    (hMm : ∀ args m Q X, plainMinMarkSpec args m Q X →
      Γ "plain_min_mark" [i64, i32, i8] [] args m Q X) :
    ∀ args m Q X, plainShrinkBlkSpec args m Q X →
      Func.wp Γ plain_shrink_blk_body args m Q X := by
  rintro ⟨h, beg, end_b, blvl, max_tr, ⟨⟩⟩ m Q X
    ⟨c, F0, s, R, rfl, hcore, hmin0, hno8_0, hbeg1, hbeg_end, hend_tl, htl_mv, hblvl_pos,
      hblvl_lt, hEnt0, hblk_spec, hkeep_spec, hm, hQ⟩
  unfold Func.wp plain_shrink_blk_body
  ml_ld load_arena_tmp_lits hm; ml_ld load_arena_mark hm
  ml_ld load_arena_level hm; ml_ld load_arena_reason hm
  ml_ld load_arena_trail hm; ml_ld load_arena_shrink_stk_ptr hm
  ml_ld load_arena_arena_ptr hm; ml_ld load_arena_mv hm
  ml_lets
  have hmv := c.hmv; unfold dimacsBound at hmv
  have hlen0 := hcore.lengths
  let keep0 := ((s.tmp.take s.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat
  have hblk_lt : ∀ j, beg.toNat ≤ j → j < end_b.toNat →
      (s.tmp[j]?.getD 0#32).toNat / 2 < c.mv := fun j hj1 hj2 => by
    have := (hblk_spec j hj1 hj2).1; omega
  refine wp_loop_group (ts := [i64, i64]) (fun n (slen_bv, k_bv, ()) m1 =>
      ∃ (mrk1 : List (BitVec 8)) (sstk1 : List (BitVec 32)),
        n = end_b.toNat - k_bv.toNat ∧ beg.toNat ≤ k_bv.toNat ∧ k_bv.toNat ≤ end_b.toNat ∧
        slen_bv.toNat = k_bv.toNat - beg.toNat ∧
        ShrinkBaseInv c F0 s mrk1 s.min_stk s.min_clr s.min_clr_len s.min_clr_full
          sstk1 slen_bv.toNat keep0 ∧
        (∀ j, beg.toNat ≤ j → j < k_bv.toNat →
          (mrk1[(s.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8) ∧
        (∀ j < slen_bv.toNat, (mrk1[(sstk1[j]?.getD 0#32).toNat]?.getD 0#8 &&& 8#8) ≠ 0#8) ∧
        (∀ w < c.mv, (mrk1[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
          ∃ j, beg.toNat ≤ j ∧ j < k_bv.toNat ∧ (s.tmp[j]?.getD 0#32).toNat / 2 = w) ∧
        trailCount8 s.trl mrk1 (min (max_tr.toNat + 1) s.trail_end) ≤ slen_bv.toNat ∧
        (PlainMem c (shrinkBlkSt s s.tmp mrk1 s.min_stk s.min_clr s.min_clr_len s.min_clr_full
          sstk1) ⋆ R) m1) ?_ ?_
  · rintro J1 n ⟨slen_bv, k_bv, ⟨⟩⟩ m1 hJ1
      ⟨mrk1, sstk1, rfl, hbk1, hke1, hsl_eq, hb1, hblk_k, hsstk_k, h8_k, hcnt_k, hm1⟩
    rw [Blocks.get_here]; ml_lets; ml_jnz; refine ⟨fun hult => ?_, fun hdone => ?_⟩
    · c0_cond hult
      have hmrk_len : mrk1.length = c.mv := hb1.mrk_len
      have hsstk_len : sstk1.length = c.mv := hb1.sstk_len
      have hsl_le : slen_bv.toNat ≤ c.mv := hb1.slen_le
      have hk_tmp : k_bv.toNat < s.tmp.length := by rw [hlen0.tmp_len_arr]; omega
      have hv_lt : (s.tmp[k_bv.toNat]?.getD 0#32).toNat / 2 < c.mv :=
        hblk_lt k_bv.toNat hbk1 hult
      ml_ld c0_load_arena_tmp (s := shrinkBlkSt s s.tmp mrk1 s.min_stk s.min_clr s.min_clr_len
        s.min_clr_full sstk1) (i := k_bv)
        (by dsimp only [shrinkBlkSt]; rw [hlen0.tmp_len_arr]; omega) hm1
      let lit := s.tmp[k_bv.toNat]'hk_tmp
      let v := lit >>> 1
      have hv_nat : v.toNat = (s.tmp[k_bv.toNat]?.getD 0#32).toNat / 2 := by
        dsimp only [v, lit]; rw [List.getElem?_eq_getElem hk_tmp, Option.getD_some, bv32_lshr_1]
      have hv_lt' : v.toNat < c.mv := by rw [hv_nat]; exact hv_lt
      have hv64 : (v.setWidth 64).toNat = v.toNat := bv_c0_zext32_64 v
      ml_ld c0_load_arena_mrk (s := shrinkBlkSt s s.tmp mrk1 s.min_stk s.min_clr s.min_clr_len
        s.min_clr_full sstk1) (i := v.setWidth 64)
        (by dsimp only [shrinkBlkSt]; rw [hmrk_len, hv64]; exact hv_lt') hm1
      ml_lets
      ml_st m_s1, hm_s := c0_store_arena_mrk (s := shrinkBlkSt s s.tmp mrk1 s.min_stk s.min_clr
        s.min_clr_len s.min_clr_full sstk1) (i := v.setWidth 64) _
        (by dsimp only [shrinkBlkSt]; rw [hmrk_len, hv64]; exact hv_lt') hm1
      let mrk2 := mrk1.set v.toNat (mrk1[v.toNat]?.getD 0#8 ||| 8#8)
      have hm_s1 := hm_s
      change (PlainMem c _ ⋆ R) m_s1 at hm_s1
      dsimp only [shrinkBlkSt, v, lit] at hm_s1
      simp only [bv_c0_zext32_64, bv32_lshr_1, Arg.val_var, bv8_or8_c0] at hm_s1
      have hm_mrk1 : (s.tmp[k_bv.toNat]'hk_tmp).toNat / 2 < mrk1.length := by
        have : v.toNat < mrk1.length := by rw [hmrk_len]; exact hv_lt'
        dsimp only [v, lit] at this; rwa [bv32_lshr_1] at this
      have hm_s1' : (PlainMem c (shrinkBlkSt s s.tmp mrk2 s.min_stk s.min_clr s.min_clr_len
          s.min_clr_full sstk1) ⋆ R) m_s1 := by
        dsimp only [shrinkBlkSt, mrk2, v, lit]
        rw [bv32_lshr_1, List.getElem?_eq_getElem hm_mrk1, Option.getD_some]
        exact hm_s1
      have hsl_stk : slen_bv.toNat < (shrinkBlkSt s s.tmp mrk2 s.min_stk s.min_clr s.min_clr_len
          s.min_clr_full sstk1).heur.shrink_stk.length := by
        dsimp only [shrinkBlkSt]; rw [hsstk_len]; omega
      ml_st m_s2, hm_s2 := c0_store_arena_shrink_stk (s := shrinkBlkSt s s.tmp mrk2 s.min_stk
        s.min_clr s.min_clr_len s.min_clr_full sstk1) (i := slen_bv) v hsl_stk hm_s1'
      ml_lets
      let sstk2 := sstk1.set slen_bv.toNat v
      have hm_s2' : (PlainMem c (shrinkBlkSt s s.tmp mrk2 s.min_stk s.min_clr s.min_clr_len
          s.min_clr_full sstk2) ⋆ R) m_s2 := by
        dsimp only [shrinkBlkSt, sstk2] at hm_s2 ⊢; exact hm_s2
      have hmin2 := plainMinMarkInv_set_bit8 (shrinkBaseInv_core hcore hb1) hb1.min_inv hv_lt'
      change PlainMinMarkInv c F0 (shrinkBlkSt s s.tmp mrk2 s.min_stk s.min_clr s.min_clr_len
        s.min_clr_full sstk1) keep0 at hmin2
      have hmin2' : PlainMinMarkInv c F0 (shrinkBlkSt s s.tmp mrk2 s.min_stk s.min_clr
          s.min_clr_len s.min_clr_full sstk2) keep0 :=
        ⟨hmin2.mrk_dom, hmin2.clr_cov, hmin2.rem_sound⟩
      obtain ⟨hmono2, hmono8⟩ := shrink_set_bit8_monos hmrk_len hv_lt'
      have hm2_v : (mrk2[v.toNat]?.getD 0#8 &&& 8#8) ≠ 0#8 := by
        dsimp only [mrk2]; rw [List.getElem?_set_self (by omega), Option.getD_some]
        exact bv8_and8_of_or8 _
      have hb2 : ShrinkBaseInv c F0 s mrk2 s.min_stk s.min_clr s.min_clr_len s.min_clr_full
          sstk2 (slen_bv.toNat + 1) keep0 := by
        refine ⟨by simp [mrk2, hb1.mrk_len], hb1.mstk_len, hb1.mclr_len, hb1.mcl_le,
          by simp [sstk2, hb1.sstk_len], by omega, hmin2',
          fun w hw h2 => hmono2 w hw (hb1.mono2 w hw h2), fun w hw h8w => ?_, fun j hj => ?_⟩
        · by_cases hwe : w = v.toNat
          · subst w; refine ⟨slen_bv.toNat, by omega, ?_⟩
            dsimp only [sstk2]; rw [List.getElem?_set_self (by omega), Option.getD_some]
          · dsimp only [mrk2] at h8w; rw [List.getElem?_set_ne (Ne.symm hwe)] at h8w
            obtain ⟨j, hj, hje⟩ := hb1.bit8_sstk w hw h8w
            refine ⟨j, by omega, ?_⟩
            dsimp only [sstk2]; rwa [List.getElem?_set_ne (by omega)]
        · dsimp only [sstk2]; by_cases hjs : j = slen_bv.toNat
          · subst j; rw [List.getElem?_set_self (by omega), Option.getD_some]; exact hv_lt'
          · rw [List.getElem?_set_ne (Ne.symm hjs)]; exact hb1.sstk_lt j (by omega)
      have hsl1 : (slen_bv + 1).toNat = slen_bv.toNat + 1 := min_bv64_add1 (by omega)
      have hk1 : (k_bv + 1).toNat = k_bv.toNat + 1 := min_bv64_add1 (by omega)
      refine hJ1 (end_b.toNat - (k_bv + 1).toNat) (slen_bv + 1, k_bv + 1, ()) _ (by omega)
        ⟨mrk2, sstk2, rfl, by omega, by omega, by rw [hsl1, hk1]; omega, by rw [hsl1]; exact hb2,
          fun j hj1 hj2 => ?_, fun j hj => ?_, fun w hw h8w => ?_, ?_, hm_s2'⟩
      · rw [hk1] at hj2; by_cases hjk : j = k_bv.toNat
        · subst j; rwa [← hv_nat]
        · exact hmono8 _ (hblk_lt j hj1 (by omega)) (hblk_k j hj1 (by omega))
      · rw [hsl1] at hj; dsimp only [sstk2]; by_cases hjs : j = slen_bv.toNat
        · subst j; rw [List.getElem?_set_self (by omega), Option.getD_some]; exact hm2_v
        · rw [List.getElem?_set_ne (Ne.symm hjs)]
          exact hmono8 _ (hb1.sstk_lt j (by omega)) (hsstk_k j (by omega))
      · rw [hk1]; by_cases hwe : w = v.toNat
        · subst w; exact ⟨k_bv.toNat, hbk1, by omega, hv_nat.symm⟩
        · dsimp only [mrk2] at h8w; rw [List.getElem?_set_ne (Ne.symm hwe)] at h8w
          obtain ⟨j, hj1, hj2, hjv⟩ := h8_k w hw h8w; exact ⟨j, hj1, by omega, hjv⟩
      · rw [hsl1]
        have htl := trailCount8_set_bit8_le (trl := s.trl) (mrk := mrk1)
          (fun i j hi hj heq => hcore.trail_vars_nodup i j (by omega) (by omega) heq)
          v.toNat (min (max_tr.toNat + 1) s.trail_end) (Nat.min_le_right _ _)
        dsimp only [mrk2]; omega
    · c0_cond hdone
      have hk_end : k_bv = end_b := BitVec.eq_of_toNat_eq (by omega)
      subst k_bv
      let AfterInv := ShrinkAfterInv c F0 s blvl beg.toNat end_b.toNat keep0 R
      refine wp_join_group (ts := [i64, i64, .bool, i32, i64]) AfterInv ?_ ?_
      · rintro J_am xs m_a ha; rw [Blocks.get_here]
        exact shrink_blk_after_wp hMm hcore hbeg1 hbeg_end hend_tl htl_mv hEnt0
          (fun k hk1 hk2 => (hblk_spec k hk1 hk2).2.2.1) hkeep_spec hQ ha
      · rintro J_am hJ_am
        refine wp_loop_group (ts := [i64, i64, .bool, i32, i64])
          (ShrinkMainInv c F0 s blvl beg.toNat end_b.toNat keep0 R) ?_ ?_
        · rintro Jm n ⟨open_c, slen_c, failed_c, uip_c, t_c, ⟨⟩⟩ m_c hJm
            ⟨mrk_c, mstk_c, mclr_c, sstk_c, mcl_c, mcf_c, rfl, hb_c, hblk_c, hsstk_c, hm_c, hok⟩
          clear hQ hmin0 hno8_0 hEnt0 hkeep_spec hblk_spec hm max_tr m hJ1 hb1 hsstk_k hcnt_k hm1
          clear hbk1 hke1 hsl_eq hblk_k h8_k hdone J1 slen_bv m1 mrk1 sstk1
          rw [Blocks.get_here]; ml_lets; ml_jnz; refine ⟨fun hfail => ?_, fun hnfail => ?_⟩
          · ml_lets; apply hJ_am
            exact ⟨mrk_c, mstk_c, mclr_c, sstk_c, mcl_c, mcf_c, hb_c, hsstk_c, hm_c,
              fun h => by cases hfail.symm.trans h⟩
          · obtain ⟨hop_pos, hop_le, h8_c, hcnt_c⟩ := hok hnfail
            have hcore_c := shrinkBaseInv_core hcore hb_c
            let st_c := shrinkBlkSt s s.tmp mrk_c mstk_c mclr_c mcl_c mcf_c sstk_c
            let InnerOutInv : Tup Val [.bool, i32, i64] → Mem 64 → Prop :=
              fun (failed_in, uip_in, t_in, ()) m_in =>
                m_in = m_c ∧
                (failed_in = false →
                  t_in.toNat < s.trail_end ∧ t_in.toNat ≤ t_c.toNat ∧
                  uip_in = s.trl[t_in.toNat]?.getD 0#32 ∧
                  (mrk_c[uip_in.toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8 ∧
                  ∀ j, t_in.toNat < j → j < s.trail_end → j ≤ t_c.toNat →
                    (mrk_c[(s.trl[j]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 8#8) = 0#8)
            refine wp_join_group (ts := [.bool, i32, i64]) InnerOutInv ?_ ?_
            · rintro J_in ⟨failed_in, uip_in, t_in, ⟨⟩⟩ m_in ⟨hm_in_eq, hin⟩
              subst m_in
              rw [Blocks.get_here]; ml_jnz; refine ⟨fun hfi => ?_, fun hnfi => ?_⟩
              · ml_lets; apply hJ_am
                exact ⟨mrk_c, mstk_c, mclr_c, sstk_c, mcl_c, mcf_c, hb_c, hsstk_c, hm_c,
                  fun h => by cases hfi.symm.trans h⟩
              · dsimp only at hnfi
                obtain ⟨ht_te, ht_tc, huip_in_eq, huip_in_8, hzero_gap⟩ := hin hnfi
                clear hin; subst failed_in
                have ht_tl : t_in.toNat < s.trail_end := ht_te
                have huip_in_eq' : (s.trl[t_in.toNat]?.getD 0#32).toNat = uip_in.toNat :=
                  congrArg BitVec.toNat huip_in_eq.symm
                have huip_in_lt : uip_in.toNat < 2 * c.mv := by
                  rw [← huip_in_eq']; exact hcore.trail_lits_lt _ ht_te
                have htc_zero : ∀ j, t_in.toNat + 1 ≤ j → j < min (t_c.toNat + 1) s.trail_end →
                    (mrk_c[(s.trl[j]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 8#8) = 0#8 :=
                  fun j hj1 hj2 => hzero_gap j (by omega) (by omega) (by omega)
                have htc_gap := trailCount8_eq_of_zero_range (trl := s.trl) (mrk := mrk_c)
                  (by omega : t_in.toNat + 1 ≤ min (t_c.toNat + 1) s.trail_end) htc_zero
                have htc_nz := trailCount8_step_nz (trl := s.trl) (mrk := mrk_c)
                  (n := t_in.toNat) (by rwa [huip_in_eq'])
                have hcnt_in : trailCount8 s.trl mrk_c t_in.toNat ≤ open_c.toNat - 1 := by omega
                ml_lets; ml_jnz; refine ⟨fun hop1 => ?_, fun hop_ne1 => ?_⟩
                · c0_cond hop1
                  have hop1' : open_c.toNat = 1 := by rw [hop1]; rfl
                  have hcnt0 : trailCount8 s.trl mrk_c t_in.toNat = 0 := by omega
                  ml_lets; apply hJ_am
                  refine ⟨mrk_c, mstk_c, mclr_c, sstk_c, mcl_c, mcf_c, hb_c, hsstk_c, hm_c,
                    fun _ _ => ⟨t_in.toNat, ht_te, huip_in_eq', huip_in_8,
                      (h8_c _ (by omega) huip_in_8).1, hblk_c, fun w hw hw8 => ?_⟩⟩
                  obtain ⟨_, idx, hidx_te, hidx_v, hdisj⟩ := h8_c w hw hw8
                  by_cases heq : idx = t_in.toNat
                  · subst heq; left; simp only [Arg.val_var]; rw [← hidx_v, huip_in_eq']
                  · by_cases hlt : idx < t_in.toNat
                    · exfalso
                      have hz := trailCount8_eq_zero_mem hcnt0 hlt
                      rw [hidx_v] at hz; exact hw8 hz
                    · rcases hdisj with htc | hres
                      · exfalso
                        have hz := hzero_gap idx (by omega) hidx_te htc
                        rw [hidx_v] at hz; exact hw8 hz
                      · exact Or.inr ⟨idx, hidx_te, by omega, hidx_v, hres⟩
                · have hop_ge2 : 2 ≤ open_c.toNat := by
                    by_cases h1 : open_c = 1#64
                    · simp [h1] at hop_ne1
                    · have h1v : (1#64 : BitVec 64).toNat = 1 := rfl
                      have hne : open_c.toNat ≠ 1 := fun h =>
                        h1 (BitVec.eq_of_toNat_eq (by rw [h, h1v]))
                      omega
                  ml_lets; ml_jnz; refine ⟨fun ht0 => ?_, fun ht_ne0 => ?_⟩
                  · ml_lets; apply hJ_am
                    exact ⟨mrk_c, mstk_c, mclr_c, sstk_c, mcl_c, mcf_c, hb_c, hsstk_c, hm_c,
                      fun h => by cases h⟩
                  · c0_cond ht_ne0
                    have ht_pos : 1 ≤ t_in.toNat := bv64_pos_of_ne0 ht_ne0
                    let t_next := t_in - 1
                    have ht_next : t_next.toNat = t_in.toNat - 1 := min_bv64_sub1 ht_pos
                    have hmin_tn : min (t_next.toNat + 1) s.trail_end = t_in.toNat := by omega
                    have hcnt_pre : trailCount8 s.trl mrk_c
                        (min (t_next.toNat + 1) s.trail_end) ≤ open_c.toNat - 1 := by
                      rwa [hmin_tn]
                    have h8_pre : ∀ w < c.mv, (mrk_c[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
                        (s.lvl[w]?.getD 0#32).toNat = blvl.toNat ∧
                        ∃ idx < s.trail_end, (s.trl[idx]?.getD 0#32).toNat / 2 = w ∧
                          (idx ≤ t_next.toNat ∨ ShrinkResolved c F0 s mrk_c idx ∨
                            idx = t_in.toNat) := by
                      intro w hw hw8
                      obtain ⟨hl, idx, hidx_te, hidx_v, hdisj⟩ := h8_c w hw hw8
                      refine ⟨hl, idx, hidx_te, hidx_v, ?_⟩
                      rcases hdisj with hle | hres
                      · by_cases heq : idx = t_in.toNat
                        · exact Or.inr (Or.inr heq)
                        · by_cases hlt : idx < t_in.toNat
                          · exact Or.inl (by omega)
                          · exfalso
                            have hz := hzero_gap idx (by omega) hidx_te hle
                            rw [hidx_v] at hz; exact hw8 hz
                      · exact Or.inr (Or.inl hres)
                    have huip_v_rsn : ((uip_in >>> 1).setWidth 64).toNat < st_c.rsns.length := by
                      dsimp only [st_c, shrinkBlkSt]
                      rw [hlen0.rsns_len, bv_c0_zext32_64, bv32_lshr_1]; omega
                    ml_ld c0_load_arena_rsns (s := st_c) (i := (uip_in >>> 1).setWidth 64)
                      huip_v_rsn hm_c
                    let rsn := s.rsns[(uip_in >>> 1).setWidth 64 |>.toNat]'huip_v_rsn
                    have hrs_idx : ((uip_in >>> 1).setWidth 64).toNat =
                        (s.trl[t_in.toNat]?.getD 0#32).toNat / 2 := by
                      rw [bv_c0_zext32_64, bv32_lshr_1, huip_in_eq']
                    have hrsn_eq : rsn = s.rsns[(s.trl[t_in.toNat]?.getD 0#32).toNat / 2]?.getD
                        0xFFFFFFFF#32 := by
                      dsimp only [rsn]
                      rw [List.getElem?_eq_getElem (by rw [hlen0.rsns_len]; omega),
                        Option.getD_some]
                      congr 1
                    ml_lets; ml_jnz; refine ⟨fun hrsn_ff => ?_, fun hrsn_ne => ?_⟩
                    · ml_lets; apply hJ_am
                      exact ⟨mrk_c, mstk_c, mclr_c, sstk_c, mcl_c, mcf_c, hb_c, hsstk_c, hm_c,
                        fun h => by cases h⟩
                    · c0_cond hrsn_ne
                      have hrsn_ne' : s.rsns[(s.trl[t_in.toNat]?.getD 0#32).toNat / 2]?.getD
                          0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
                        rw [getElem?_getD_of_getElem 0xFFFFFFFF#32 (rfl : s.rsns = st_c.rsns)
                          (congrArg (· / 2) huip_in_eq')]
                        exact hrsn_ne
                      have hrs := hcore.reason_inv t_in.toNat ht_te hrsn_ne'
                      let StepInv := ShrinkStepInv c F0 s blvl beg.toNat end_b.toNat keep0
                        t_next.toNat t_in.toNat R
                      refine wp_join_group (ts := [i64, i64, .bool]) StepInv ?_ ?_
                      · rintro J_sj ⟨open', slen', failed', ⟨⟩⟩ m'
                          ⟨mrk', mstk', mclr', sstk', mcl', mcf', hb', hblk', hsstk', hm', hok'⟩
                        rw [Blocks.get_here]; ml_lets; ml_jnz
                        refine ⟨fun hf' => ?_, fun hnf' => ?_⟩
                        · ml_lets; apply hJ_am
                          exact ⟨mrk', mstk', mclr', sstk', mcl', mcf', hb', hsstk', hm',
                            fun h => by cases hf'.symm.trans h⟩
                        · obtain ⟨hop2', hopl', h8', hcnt', hrc'⟩ := hok' hnf'
                          have hopm1 : (open' - 1).toNat = open'.toNat - 1 :=
                            min_bv64_sub1 (by omega)
                          have hdec_m : (if (false : Bool) = true then 0 else
                              min t_next.toNat s.trail_end + 1) <
                              (if failed_c = true then 0 else min t_c.toNat s.trail_end + 1) := by
                            simp only [hnfail, Bool.false_eq_true, ↓reduceIte]; omega
                          subst failed'; ml_lets
                          refine hJm (if (false : Bool) = true then 0 else
                              min t_next.toNat s.trail_end + 1)
                            (open' - 1, slen', false, uip_in, t_next, ()) m' hdec_m
                            ⟨mrk', mstk', mclr', sstk', mcl', mcf', rfl, hb', hblk', hsstk', hm',
                              fun _ => ⟨by omega, by omega, fun w hw hw8 => ?_, by omega⟩⟩
                          obtain ⟨hl, idx, hidx_te, hidx_v, hdisj⟩ := h8' w hw hw8
                          refine ⟨hl, idx, hidx_te, hidx_v, ?_⟩
                          rcases hdisj with h1 | h2 | rfl
                          · exact Or.inl h1
                          · exact Or.inr h2
                          · exact Or.inr hrc'
                      · rintro J_sj hJ_sj
                        ml_lets; ml_jnz; refine ⟨fun hbin => ?_, fun hcl_b => ?_⟩
                        · c0_cond hbin
                          have hbin' : (s.rsns[(s.trl[t_in.toNat]?.getD 0#32).toNat / 2]?.getD
                              0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 := by
                            rw [getElem?_getD_of_getElem 0xFFFFFFFF#32 (rfl : s.rsns = st_c.rsns)
                              (congrArg (· / 2) huip_in_eq')]
                            exact hbin
                          dsimp only at hrs; simp only [eq_true hbin', ↓reduceIte] at hrs
                          obtain ⟨hot_lt, hent_b, kot, hkot_lt, hkot_eq⟩ := hrs
                          let ot := rsn &&& 0x7FFFFFFF#32
                          let ov := ot >>> 1
                          have hot_eq : ot.toNat = ((s.rsns[(s.trl[t_in.toNat]?.getD 0#32).toNat /
                              2]?.getD 0xFFFFFFFF#32) &&& 0x7FFFFFFF#32).toNat := by
                            dsimp only [ot]; rw [← hrsn_eq]
                          have hot_lt' : ot.toNat < 2 * c.mv := by rw [hot_eq]; exact hot_lt
                          have hov_nat : ov.toNat = ot.toNat / 2 := bv32_lshr_1 ot
                          have hov_lt : ov.toNat < c.mv := by rw [hov_nat]; omega
                          have hcov_of : ∀ {mrk' : List (BitVec 8)},
                              ((s.lvl[ot.toNat / 2]?.getD 0#32).toNat = 0 ∨
                                (mrk'[ot.toNat / 2]?.getD 0#8 &&& 2#8) ≠ 0#8 ∨
                                (mrk'[ot.toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8) →
                              RsnCov c F0 s (fun w =>
                                (mrk'[w]?.getD 0#8 &&& 2#8) ≠ 0#8 ∨
                                (mrk'[w]?.getD 0#8 &&& 8#8) ≠ 0#8) t_in.toNat := fun hdep => by
                            simp only [RsnCov, hrsn_ne', eq_true hbin', ↓reduceIte, ne_eq,
                              not_false_eq_true, true_and]
                            exact ⟨hot_lt, hent_b, kot, hkot_lt, hkot_eq, by
                              rw [← hot_eq]; rcases hdep with h0 | h2 | h8
                              · exact Or.inl h0
                              · exact Or.inr (Or.inl h2)
                              · exact Or.inr (Or.inr h8)⟩
                          ml_lets
                          refine wp_join_group (ts := [i64, i64, .bool]) StepInv ?_ ?_
                          · rintro J_b ⟨open', slen', failed', _⟩ m' h'
                            rw [Blocks.get_here]; ml_lets; exact hJ_sj _ _ h'
                          · rintro J_b hJ_b
                            ml_lets; ml_jnz; refine ⟨fun hov_ok => ?_, fun hov_oob => ?_⟩
                            · c0_cond hov_ok
                              have hov_lvl_l : (ov.setWidth 64).toNat < st_c.lvl.length := by
                                dsimp only [st_c, shrinkBlkSt]
                                rw [hlen0.lvl_len, bv_c0_zext32_64]; exact hov_lt
                              ml_ld c0_load_arena_lvl (s := st_c) (i := ov.setWidth 64)
                                hov_lvl_l hm_c
                              ml_lets; ml_jnz; refine ⟨fun hlpos => ?_, fun hlz => ?_⟩
                              · c0_cond hlpos
                                have hov_mrk_l : (ov.setWidth 64).toNat < st_c.mrk.length := by
                                  dsimp only [st_c, shrinkBlkSt]
                                  rw [hb_c.mrk_len, bv_c0_zext32_64]; exact hov_lt
                                ml_ld c0_load_arena_mrk (s := st_c) (i := ov.setWidth 64)
                                  hov_mrk_l hm_c
                                ml_lets; ml_jnz; refine ⟨fun hno8 => ?_, fun hhas8 => ?_⟩
                                · c0_cond hno8
                                  have hno8' : (mrk_c[ov.toNat]?.getD 0#8 &&& 8#8) = 0#8 := by
                                    rw [getElem?_getD_of_getElem 0#8 (rfl : mrk_c = st_c.mrk) rfl]
                                    exact hno8
                                  refine wp_join_group (ts := [i64, i64, .bool]) StepInv ?_ ?_
                                  · rintro J_b1 ⟨open', slen', failed', _⟩ m' h'
                                    rw [Blocks.get_here]; ml_lets; exact hJ_b _ _ h'
                                  · rintro J_b1 hJ_b1
                                    ml_ld c0_load_arena_lvl (s := st_c) (i := ov.setWidth 64)
                                      hov_lvl_l hm_c
                                    ml_lets; ml_jnz; refine ⟨fun hlt_blvl => ?_, fun hge_blvl => ?_⟩
                                    · c0_cond hlt_blvl
                                      have hlov_lt : (s.lvl[ot.toNat / 2]?.getD 0#32).toNat <
                                          blvl.toNat := by
                                        rw [getElem?_getD_of_getElem 0#32 (rfl : s.lvl = st_c.lvl)
                                          hov_nat.symm]
                                        exact hlt_blvl
                                      refine wp_join_group (ts := [.bool])
                                          (fun (f', ()) m' => StepInv (open_c, slen_c, f', ()) m')
                                          ?_ ?_
                                      · rintro Jml ⟨f', ⟨⟩⟩ m' hm'
                                        rw [Blocks.get_here]; ml_lets; exact hJ_b1 _ _ hm'
                                      · rintro Jml hJml
                                        ml_ld c0_load_arena_mrk (s := st_c)
                                          (i := ov.setWidth 64) hov_mrk_l hm_c
                                        ml_lets; ml_jnz
                                        refine ⟨fun hno2 => ?_, fun hhas2 => ?_⟩
                                        · c0_cond hno2
                                          refine wp_join_group (ts := [.bool])
                                              (fun (f', ()) m' =>
                                                StepInv (open_c, slen_c, f', ()) m') ?_ ?_
                                          · rintro Jml2 ⟨f', ⟨⟩⟩ m' hm'
                                            rw [Blocks.get_here]; ml_lets
                                            exact hJml (f', ()) m' hm'
                                          · rintro Jml2 hJml2
                                            refine wp_join_group (ts := []) (ShrinkPoisonInv c F0 s
                                                beg.toNat end_b.toNat keep0 slen_c.toNat ov.toNat R)
                                                ?_ ?_
                                            · rintro Jp ⟨⟩ m'
                                                ⟨mrk_p, mstk_p, mclr_p, sstk_p, mcl_p, mcf_p, hb_p,
                                                  hblk_p, hsstk_p, hno8_p, hm_p⟩
                                              rw [Blocks.get_here]; ml_lets
                                              apply wp_call_of_spec; apply hMm
                                              refine shrink_poison_spec hcore hblk_lt hov_lt hno8_p
                                                hb_p hblk_p hsstk_p hm_p
                                                fun mrk' mstk' mclr' sstk' mcl' mcf' m_q hb' hblk'
                                                  hsstk' hm_q =>
                                                hJml2 (true, ()) m_q ⟨mrk', mstk', mclr', sstk',
                                                  mcl', mcf', hb', hblk', hsstk', hm_q,
                                                  fun h => by cases h⟩
                                            · rintro Jp hJp
                                              ml_ld c0_load_arena_mrk (s := st_c)
                                                (i := ov.setWidth 64) hov_mrk_l hm_c
                                              ml_lets; ml_jnz
                                              refine ⟨fun hpois => ?_, fun hnpois => ?_⟩
                                              · ml_lets
                                                exact hJp () m_c ⟨mrk_c, mstk_c, mclr_c, sstk_c,
                                                  mcl_c, mcf_c, hb_c, hblk_c, hsstk_c, hno8', hm_c⟩
                                              · c0_cond hnpois
                                                ml_lets; apply wp_call_of_spec; apply hMl
                                                have hno8_ml := shrinkOkInv_lvl_lt_no8
                                                  (fun w hw h8 => (h8_c w hw h8).1) hlov_lt
                                                have hot_vals : st_c.vals[ot.toNat]?.getD 0#8 =
                                                    0xFF#8 := by
                                                  dsimp only [st_c, shrinkBlkSt]
                                                  exact (hcore.vals_false_iff _ hot_lt').mpr
                                                    ⟨kot, by omega, by rw [hkot_eq, ← hot_eq]⟩
                                                refine ⟨c, F0, st_c, keep0, R, rfl, hcore_c,
                                                  hb_c.min_inv, hot_lt', hot_vals, ?_, hm_c,
                                                  fun _ mrk_ml mstk_ml mclr_ml mcl_ml mcf_ml m_ml
                                                    hlen_ml hmono_ml hbit8_ml hmin_ml hrem_ml hm_ml
                                                    => ?_⟩
                                                · intro w hw hle
                                                  exact hno8_ml w hw hle
                                                · ml_lets; dsimp only; ml_jnz
                                                  refine ⟨fun hml_ok => ?_, fun hml_fail => ?_⟩
                                                  · ml_lets; apply wp_call_of_spec; apply hMm
                                                    have hmin2_ml := (hrem_ml hml_ok).2
                                                    change PlainMinMarkInv c F0 (plainMinMarkState
                                                      c _ (ot.toNat / 2) 2#8) keep0 at hmin2_ml
                                                    rw [← hov_nat] at hmin2_ml
                                                    refine shrink_ml_ok_spec hcore hb_c hov_lt hno8'
                                                      hlen_ml hmono_ml hbit8_ml hmin_ml hmin2_ml
                                                      hblk_lt hblk_c hsstk_c h8_pre hcnt_pre hm_ml
                                                      fun mrk' mstk' mclr' sstk' mcl' mcf' m_2 hb2
                                                        _ _ hov_2 hblk2 hsstk2 h8_2 hcnt2 hm_2 =>
                                                      hJml2 (false, ()) m_2 ⟨mrk', mstk', mclr',
                                                        sstk', mcl', mcf', hb2, hblk2, hsstk2, hm_2,
                                                        fun _ => ⟨hop_ge2, hop_le, h8_2, hcnt2,
                                                          hcov_of (Or.inr (Or.inl (by
                                                            rwa [← hov_nat])))⟩⟩
                                                  · ml_lets
                                                    obtain ⟨hb_ml, hblk_ml, hsstk_ml, hno8_mlv⟩ :=
                                                      shrink_ml_fail_base hb_c hov_lt hno8' hlen_ml
                                                        hmono_ml hbit8_ml hmin_ml hblk_lt hblk_c
                                                        hsstk_c
                                                    exact hJp () m_ml ⟨mrk_ml, mstk_ml, mclr_ml,
                                                      sstk_c, mcl_ml, mcf_ml, hb_ml, hblk_ml,
                                                      hsstk_ml, hno8_mlv, hm_ml⟩
                                        · c0_cond hhas2
                                          have h2' : (mrk_c[ot.toNat / 2]?.getD 0#8 &&& 2#8) ≠
                                              0#8 := by
                                            rw [getElem?_getD_of_getElem 0#8
                                              (rfl : mrk_c = st_c.mrk) hov_nat.symm]
                                            exact hhas2
                                          ml_lets
                                          exact hJml (false, ()) m_c ⟨mrk_c, mstk_c, mclr_c,
                                            sstk_c, mcl_c, mcf_c, hb_c, hblk_c, hsstk_c, hm_c,
                                            fun _ => ⟨hop_ge2, hop_le, h8_pre, hcnt_pre,
                                              hcov_of (Or.inr (Or.inl h2'))⟩⟩
                                    · c0_cond hge_blvl
                                      dsimp only [st_c, shrinkBlkSt] at hge_blvl
                                      have hlov_ge : blvl.toNat ≤
                                          (s.lvl[ot.toNat / 2]?.getD 0#32).toNat := by
                                        rw [getElem?_getD_of_getElem 0#32
                                          (hj := by rw [hlen0.lvl_len]; exact hov_lt) rfl
                                          hov_nat.symm]
                                        omega
                                      refine wp_join_group (ts := [i64, i64, .bool]) StepInv ?_ ?_
                                      · rintro Jp ⟨open', slen', failed', _⟩ m' hp
                                        rw [Blocks.get_here]; ml_lets; exact hJ_b1 _ _ hp
                                      · rintro Jp hJp
                                        ml_lets; ml_jnz; refine ⟨fun hsl_lt => ?_, fun hsl_ge => ?_⟩
                                        · c0_cond hsl_lt
                                          have hcmv := c.hmv
                                          have hsl_lt' : slen_c.toNat < c.mv := by omega
                                          ml_ld c0_load_arena_mrk (s := st_c) (i := ov.setWidth 64)
                                            hov_mrk_l hm_c
                                          ml_lets
                                          ml_st m_s1, hm_s1 := c0_store_arena_mrk (s := st_c)
                                            (i := ov.setWidth 64) _ hov_mrk_l hm_c
                                          let mrk2 := mrk_c.set ov.toNat
                                            (mrk_c[ov.toNat]?.getD 0#8 ||| 8#8)
                                          have hm_s1' := hm_s1
                                          dsimp only [st_c, shrinkBlkSt] at hm_s1'
                                          simp only [bv_c0_zext32_64, Arg.val_var, bv8_or8_c0]
                                            at hm_s1'
                                          have hm_1 : (PlainMem c (shrinkBlkSt s s.tmp mrk2 mstk_c
                                              mclr_c mcl_c mcf_c sstk_c) ⋆ R) m_s1 := by
                                            dsimp only [shrinkBlkSt, mrk2]
                                            rw [List.getElem?_eq_getElem
                                              (by rw [hb_c.mrk_len]; exact hov_lt),
                                              Option.getD_some]
                                            exact hm_s1'
                                          have hsl_stk : slen_c.toNat < (shrinkBlkSt s s.tmp mrk2
                                              mstk_c mclr_c mcl_c mcf_c
                                              sstk_c).heur.shrink_stk.length := by
                                            dsimp only [shrinkBlkSt]
                                            rw [hb_c.sstk_len]; exact hsl_lt'
                                          ml_st m_s2, hm_s2 := c0_store_arena_shrink_stk
                                            (s := shrinkBlkSt s s.tmp mrk2 mstk_c mclr_c mcl_c mcf_c
                                              sstk_c) (i := slen_c) ov hsl_stk hm_1
                                          let sstk2 := sstk_c.set slen_c.toNat ov
                                          have hm_2 : (PlainMem c (shrinkBlkSt s s.tmp mrk2 mstk_c
                                              mclr_c mcl_c mcf_c sstk2) ⋆ R) m_s2 := by
                                            dsimp only [shrinkBlkSt, sstk2] at hm_s2 ⊢; exact hm_s2
                                          have hkot_tlim : kot ≤ t_next.toNat := by omega
                                          have huip_lvl' : (s.lvl[(s.trl[t_in.toNat]?.getD
                                              0#32).toNat / 2]?.getD 0#32).toNat = blvl.toNat := by
                                            rw [huip_in_eq']; exact (h8_c _ (by omega) huip_in_8).1
                                          obtain ⟨hb2, hblk2, hsstk2, h8_2, hcnt2, hop2, hopl2,
                                            h8_new⟩ :=
                                            shrink_step_pre_push8 hcore hb_c hblk_lt hblk_c
                                              hsstk_c h8_pre hcnt_pre hop_ge2 hop_le hsl_lt'
                                              hot_lt' ht_te huip_lvl' hkot_lt
                                              (by rw [hkot_eq, ← hot_eq]) hkot_tlim hlov_ge
                                          have hop1' : (open_c + 1).toNat = open_c.toNat + 1 :=
                                            min_bv64_add1 (by omega)
                                          have hsl1' : (slen_c + 1).toNat = slen_c.toNat + 1 :=
                                            min_bv64_add1 (by omega)
                                          ml_lets
                                          refine hJp (open_c + 1, slen_c + 1, false, ()) m_s2
                                            ⟨mrk2, mstk_c, mclr_c, sstk2, mcl_c, mcf_c,
                                              by rw [hsl1']; exact hb2, hblk2,
                                              by rw [hsl1']; exact hsstk2, hm_2,
                                              fun _ => ⟨by rw [hop1']; exact hop2,
                                                by rw [hop1', hsl1']; exact hopl2, h8_2,
                                                by rw [hop1']; exact hcnt2,
                                                hcov_of (Or.inr (Or.inr h8_new))⟩⟩
                                        · ml_lets
                                          exact hJp (open_c, slen_c, true, ()) m_c ⟨mrk_c, mstk_c,
                                            mclr_c, sstk_c, mcl_c, mcf_c, hb_c, hblk_c, hsstk_c,
                                            hm_c, fun h => by cases h⟩
                                · c0_cond hhas8
                                  have h8' : (mrk_c[ot.toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8 := by
                                    rw [getElem?_getD_of_getElem 0#8 (rfl : mrk_c = st_c.mrk)
                                      hov_nat.symm]
                                    exact hhas8
                                  ml_lets
                                  exact hJ_b (open_c, slen_c, false, ()) m_c ⟨mrk_c, mstk_c, mclr_c,
                                    sstk_c, mcl_c, mcf_c, hb_c, hblk_c, hsstk_c, hm_c,
                                    fun _ => ⟨hop_ge2, hop_le, h8_pre, hcnt_pre,
                                      hcov_of (Or.inr (Or.inr h8'))⟩⟩
                              · c0_cond hlz
                                dsimp only [st_c, shrinkBlkSt] at hlz
                                have h0v : (0 : BitVec 32).toNat = 0 := rfl; rw [h0v] at hlz
                                have hlz' : (s.lvl[ot.toNat / 2]?.getD 0#32).toNat = 0 := by
                                  rw [getElem?_getD_of_getElem 0#32
                                    (hj := by rw [hlen0.lvl_len]; exact hov_lt) rfl hov_nat.symm]
                                  omega
                                ml_lets
                                exact hJ_b (open_c, slen_c, false, ()) m_c ⟨mrk_c, mstk_c, mclr_c,
                                  sstk_c, mcl_c, mcf_c, hb_c, hblk_c, hsstk_c, hm_c,
                                  fun _ => ⟨hop_ge2, hop_le, h8_pre, hcnt_pre,
                                    hcov_of (Or.inl hlz')⟩⟩
                            · exfalso
                              change (ov.setWidth 64).ult (BitVec.ofNat 64 c.mv) = false at hov_oob
                              c0_cond hov_oob; have hcmv := c.hmv; omega
                        · c0_cond hcl_b
                          have hcl_b' : (s.rsns[(s.trl[t_in.toNat]?.getD 0#32).toNat / 2]?.getD
                              0xFFFFFFFF#32 &&& 0x80000000#32) = 0#32 := by
                            rw [getElem?_getD_of_getElem 0xFFFFFFFF#32 (rfl : s.rsns = st_c.rsns)
                              (congrArg (· / 2) huip_in_eq')]
                            exact hcl_b
                          dsimp only at hrs
                          simp only [hcl_b', ne_eq, not_true_eq_false, ↓reduceIte] at hrs
                          obtain ⟨href, hng, hall_q⟩ := hrs
                          have hwf := hcore.arena.refs_wf _ href
                          have hbd : rsn.toNat + 3 + arenaClauseSize s rsn.toNat ≤ s.arena_len :=
                            by have := hwf.2.2.1; have := hwf.2.2.2.1; rw [hrsn_eq]; omega
                          have hbd_arr : rsn.toNat + 3 + arenaClauseSize s rsn.toNat ≤
                              s.arena.length := by
                            rw [hlen0.arena_len_arr]; have := hlen0.arena_len_le; omega
                          have hsz_ge3 : 3 ≤ arenaClauseSize s rsn.toNat := by
                            rw [hrsn_eq]; exact hwf.2.1
                          have hr3_le : rsn.toNat + 3 ≤ s.arena_len := by omega
                          have har_cap := c.harena; unfold dimacsBound at har_cap
                          have hal_le := hlen0.arena_len_le
                          ml_ld load_arena_len hm_c
                          ml_lets; ml_jnz; refine ⟨fun hoob1 => ?_, fun hin1 => ?_⟩
                          · exfalso
                            change (BitVec.ofNat 64 s.arena_len).ult (rsn.setWidth 64 + 3) = true
                              at hoob1
                            exact absurd (bv64_lt_zext32_add3 (by omega) rsn hoob1) (by omega)
                          · have hrs2_s : (rsn.setWidth 64 + 2).toNat < s.arena.length := by
                              rw [hlen0.arena_len_arr, bv64_zext32_add2]; omega
                            have hrs2_l : (rsn.setWidth 64 + 2).toNat < st_c.arena.length := hrs2_s
                            ml_ld c0_load_arena_arena (s := st_c) (i := rsn.setWidth 64 + 2)
                              hrs2_l hm_c
                            let csz := s.arena[(rsn.setWidth 64 + 2).toNat]'hrs2_s
                            have hidx2 : (rsn.setWidth 64 + 2).toNat = rsn.toNat + 2 :=
                              bv64_zext32_add2 rsn
                            have hcsz_nat : csz.toNat = arenaClauseSize s rsn.toNat :=
                              congrArg BitVec.toNat (getElem?_getD_of_getElem 0#32
                                (hj := hrs2_s) rfl hidx2.symm).symm
                            ml_lets; ml_jnz; refine ⟨fun hsz_bad => ?_, fun hsz_ok => ?_⟩
                            · exfalso; change csz.ult 3#32 = true at hsz_bad
                              c0_cond hsz_bad; omega
                            · ml_ld load_arena_len hm_c
                              ml_lets; ml_jnz; refine ⟨fun hoob2 => ?_, fun hin2 => ?_⟩
                              · exfalso
                                change (BitVec.ofNat 64 s.arena_len).ult
                                  (rsn.setWidth 64 + 3 + csz.setWidth 64) = true at hoob2
                                exact absurd (bv64_lt_zext32_add3_add (by omega) rsn csz hoob2)
                                  (by omega)
                              · ml_lets
                                refine wp_join_group (ts := [i64, i64, .bool, i32])
                                    (fun (open', slen', failed', _) m' =>
                                      StepInv (open', slen', failed', ()) m') ?_ ?_
                                · rintro Jcl ⟨open', slen', failed', _, _⟩ m' hcl_done
                                  rw [Blocks.get_here]; ml_lets; exact hJ_sj _ _ hcl_done
                                · rintro Jcl hJcl
                                  let ClLoopInv := ShrinkClInv c F0 s blvl beg.toNat end_b.toNat
                                    keep0 t_next.toNat t_in.toNat csz.toNat rsn.toNat R
                                  refine wp_loop_group (ts := [i64, i64, i32]) ClLoopInv ?_ ?_
                                  · rintro J4 n ⟨open_i, slen_i, i_bv, ⟨⟩⟩ m_i hJ4
                                      ⟨rfl, hic, mrk_i, mstk_i, mclr_i, sstk_i, mcl_i, mcf_i, hb_i,
                                        hblk_i, hsstk_i, hm_i, hop_i, hopl_i, h8_i, hcnt_i,
                                        hpref_i⟩
                                    clear AfterInv J_am hJ_am Jm hJm hok hnfail hop_pos hop_le
                                    clear hcnt_c InnerOutInv J_in ht_tc huip_in_eq hzero_gap
                                    clear ht_tl htc_zero htc_gap htc_nz hcnt_in hop_ne1 hop_ge2
                                    clear ht_ne0 ht_pos hmin_tn h8_pre hcnt_pre hwf hbd hsz_ge3
                                    clear hr3_le hin1 hidx2 hsz_ok hin2 hb_c hblk_c hsstk_c hm_c
                                    clear hrs_idx hrsn_ne
                                    rw [Blocks.get_here]; ml_lets; ml_jnz
                                    refine ⟨fun hilt => ?_, fun hidone => ?_⟩
                                    · c0_cond hilt
                                      have hst_i_core := shrinkBaseInv_core hcore hb_i
                                      let st_i := shrinkBlkSt s s.tmp mrk_i mstk_i mclr_i mcl_i
                                        mcf_i sstk_i
                                      have hi_lt_sz : i_bv.toNat < arenaClauseSize s rsn.toNat := by
                                        rw [← hcsz_nat]; exact hilt
                                      have hix : (rsn.setWidth 64 + 3 + i_bv.setWidth 64).toNat =
                                          rsn.toNat + 3 + i_bv.toNat :=
                                        bv64_zext32_add3_add rsn i_bv
                                      have hq_s : (rsn.setWidth 64 + 3 + i_bv.setWidth 64).toNat <
                                          s.arena.length := by rw [hix]; omega
                                      have hq_idx : (rsn.setWidth 64 + 3 + i_bv.setWidth 64).toNat <
                                          st_i.arena.length := hq_s
                                      ml_ld c0_load_arena_arena (s := st_i)
                                        (i := rsn.setWidth 64 + 3 + i_bv.setWidth 64) hq_idx hm_i
                                      let ot := s.arena[(rsn.setWidth 64 + 3 +
                                        i_bv.setWidth 64).toNat]'hq_s
                                      let ov := ot >>> 1
                                      have hot_nat : ot.toNat = (s.arena[rsn.toNat + 3 +
                                          i_bv.toNat]?.getD 0#32).toNat :=
                                        congrArg BitVec.toNat (getElem?_getD_of_getElem 0#32
                                          (hj := hq_s) rfl hix.symm).symm
                                      have hot_mem : ot.toNat ∈ arenaClauseLits s rsn.toNat := by
                                        rw [hot_nat, hrsn_eq]
                                        exact shrink_arena_lits_mem hcore href
                                          (by rwa [← hrsn_eq])
                                      have hot_lt : ot.toNat < 2 * c.mv := by
                                        rw [hrsn_eq] at hot_mem
                                        exact hcore.arena.lits_lt _ href hng _ hot_mem
                                      have hov_nat : ov.toNat = ot.toNat / 2 := bv32_lshr_1 ot
                                      have hov_lt : ov.toNat < c.mv := by rw [hov_nat]; omega
                                      have hcov_pref_step : ∀ {mrk' : List (BitVec 8)},
                                          (∀ w < c.mv, (mrk_i[w]?.getD 0#8 &&& 2#8) ≠ 0#8 →
                                            (mrk'[w]?.getD 0#8 &&& 2#8) ≠ 0#8) →
                                          (∀ w < c.mv, (mrk_i[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
                                            (mrk'[w]?.getD 0#8 &&& 8#8) ≠ 0#8) →
                                          (ot.toNat = (s.trl[t_in.toNat]?.getD 0#32).toNat ∨
                                            ((s.lvl[ot.toNat / 2]?.getD 0#32).toNat = 0 ∨
                                              (mrk'[ot.toNat / 2]?.getD 0#8 &&& 2#8) ≠ 0#8 ∨
                                              (mrk'[ot.toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8)) →
                                          ∀ k < (i_bv + 1).toNat,
                                            let q := (s.arena[rsn.toNat + 3 + k]?.getD 0#32).toNat
                                            q = (s.trl[t_in.toNat]?.getD 0#32).toNat ∨
                                            ∃ m < t_in.toNat, (s.trl[m]?.getD 0#32).toNat =
                                              q ^^^ 1 ∧ ((s.lvl[q / 2]?.getD 0#32).toNat = 0 ∨
                                                (mrk'[q / 2]?.getD 0#8 &&& 2#8) ≠ 0#8 ∨
                                                (mrk'[q / 2]?.getD 0#8 &&& 8#8) ≠ 0#8) := by
                                        intro mrk' hm2 hm8 hthis k hk
                                        have hi1 : (i_bv + 1).toNat = i_bv.toNat + 1 :=
                                          bv32_add1_toNat (by have := csz.isLt; omega)
                                        rw [hi1] at hk
                                        by_cases hki : k = i_bv.toNat
                                        · subst k; rw [← hot_nat]
                                          rcases hthis with hEq | hdep
                                          · exact Or.inl hEq
                                          · have hall := hall_q ot.toNat (by rwa [← hrsn_eq])
                                            rcases hall with hEq | ⟨k, hk_lt, hk_eq⟩
                                            · exact Or.inl hEq
                                            · exact Or.inr ⟨k, hk_lt, hk_eq, hdep⟩
                                        · rcases hpref_i k (by omega) with
                                            hEq | ⟨m, hm_lt, hm_eq, hdp⟩
                                          · exact Or.inl hEq
                                          · have hmemk : (s.arena[rsn.toNat + 3 + k]?.getD 0#32
                                                ).toNat ∈ arenaClauseLits s rsn.toNat := by
                                              rw [hrsn_eq]; exact shrink_arena_lits_mem hcore href
                                                (by rw [← hrsn_eq]; omega)
                                            have hqlt : (s.arena[rsn.toNat + 3 + k]?.getD 0#32
                                                ).toNat < 2 * c.mv := by
                                              rw [hrsn_eq] at hmemk ⊢
                                              exact hcore.arena.lits_lt _ href hng _ hmemk
                                            refine Or.inr ⟨m, hm_lt, hm_eq, ?_⟩
                                            rcases hdp with h0 | h2 | h8
                                            · exact Or.inl h0
                                            · exact Or.inr (Or.inl (hm2 _ (by omega) h2))
                                            · exact Or.inr (Or.inr (hm8 _ (by omega) h8))
                                      have hi1 : (i_bv + 1).toNat = i_bv.toNat + 1 :=
                                        bv32_add1_toNat (by have := csz.isLt; omega)
                                      let NextStepInv : Tup Val [i64, i64, .bool] → Mem 64 → Prop :=
                                        fun (open_n, slen_n, _, ()) m_n =>
                                          ClLoopInv (csz.toNat - (i_bv + 1).toNat)
                                            (open_n, slen_n, i_bv + 1, ()) m_n
                                      ml_lets
                                      refine wp_join_group (ts := [i64, i64, .bool])
                                          NextStepInv ?_ ?_
                                      · rintro J5 ⟨open_n, slen_n, _, ⟨⟩⟩ m_n h_n
                                        rw [Blocks.get_here]; ml_lets
                                        exact hJ4 (csz.toNat - (i_bv + 1).toNat)
                                          (open_n, slen_n, i_bv + 1, ()) m_n (by omega) h_n
                                      · rintro J5 hJ5
                                        ml_lets; ml_jnz; refine ⟨fun hot_ne => ?_,
                                          fun hot_eq_u => ?_⟩
                                        · change (ot != uip_in) = true at hot_ne; c0_cond hot_ne
                                          ml_lets; ml_jnz
                                          refine ⟨fun hov_ok => ?_, fun hov_oob => ?_⟩
                                          · c0_cond hov_ok
                                            have hov_lvl_l : (ov.setWidth 64).toNat <
                                                st_i.lvl.length := by
                                              dsimp only [st_i, shrinkBlkSt]
                                              rw [hlen0.lvl_len, bv_c0_zext32_64]; exact hov_lt
                                            ml_ld c0_load_arena_lvl (s := st_i)
                                              (i := ov.setWidth 64) hov_lvl_l hm_i
                                            ml_lets; ml_jnz
                                            refine ⟨fun hlpos => ?_, fun hlz => ?_⟩
                                            · c0_cond hlpos
                                              have hov_mrk_l : (ov.setWidth 64).toNat <
                                                  st_i.mrk.length := by
                                                dsimp only [st_i, shrinkBlkSt]
                                                rw [hb_i.mrk_len, bv_c0_zext32_64]; exact hov_lt
                                              ml_ld c0_load_arena_mrk (s := st_i)
                                                (i := ov.setWidth 64) hov_mrk_l hm_i
                                              ml_lets; ml_jnz
                                              refine ⟨fun hno8 => ?_, fun hhas8 => ?_⟩
                                              · c0_cond hno8
                                                have hno8' : (mrk_i[ov.toNat]?.getD 0#8 &&& 8#8) =
                                                    0#8 := by
                                                  rw [getElem?_getD_of_getElem 0#8
                                                    (rfl : mrk_i = st_i.mrk) rfl]
                                                  exact hno8
                                                refine wp_join_group (ts := [i64, i64, .bool])
                                                    NextStepInv ?_ ?_
                                                · rintro J6 ⟨op, sl, fl, ⟨⟩⟩ m_n hn
                                                  rw [Blocks.get_here]; ml_lets
                                                  exact hJ5 (op, sl, fl, ()) m_n hn
                                                · rintro J6 hJ6
                                                  ml_ld c0_load_arena_lvl (s := st_i)
                                                    (i := ov.setWidth 64) hov_lvl_l hm_i
                                                  ml_lets; ml_jnz
                                                  refine ⟨fun hlt_blvl => ?_, fun hge_blvl => ?_⟩
                                                  · c0_cond hlt_blvl
                                                    have hlov_lt :
                                                        (s.lvl[ot.toNat / 2]?.getD 0#32).toNat <
                                                        blvl.toNat := by
                                                      rw [getElem?_getD_of_getElem 0#32
                                                        (rfl : s.lvl = st_i.lvl) hov_nat.symm]
                                                      exact hlt_blvl
                                                    refine wp_join_group (ts := [.bool])
                                                        (fun (_, ()) m_n =>
                                                          NextStepInv (open_i, slen_i, false, ())
                                                            m_n) ?_ ?_
                                                    · rintro J7 ⟨fl, ⟨⟩⟩ m_n hn
                                                      rw [Blocks.get_here]; ml_lets
                                                      exact hJ6 (open_i, slen_i, fl, ()) m_n hn
                                                    · rintro J7 hJ7
                                                      ml_ld c0_load_arena_mrk (s := st_i)
                                                        (i := ov.setWidth 64) hov_mrk_l hm_i
                                                      ml_lets; ml_jnz
                                                      refine ⟨fun hno2 => ?_, fun hhas2 => ?_⟩
                                                      · c0_cond hno2
                                                        refine wp_join_group (ts := [])
                                                            (ShrinkPoisonInv c F0 s beg.toNat
                                                              end_b.toNat keep0 slen_i.toNat
                                                              ov.toNat R) ?_ ?_
                                                        · rintro J8 ⟨⟩ m'
                                                            ⟨mrk_p, mstk_p, mclr_p, sstk_p, mcl_p,
                                                              mcf_p, hb_p, hblk_p, hsstk_p, hno8_p,
                                                              hm_p⟩
                                                          rw [Blocks.get_here]; ml_lets
                                                          apply wp_call_of_spec; apply hMm
                                                          refine shrink_poison_spec hcore hblk_lt
                                                            hov_lt hno8_p hb_p hblk_p hsstk_p hm_p
                                                            fun mrk' mstk' mclr' sstk' mcl' mcf' m_q
                                                              hb' hblk' hsstk' hm_q =>
                                                            hJcl (open_i, slen_i, true, i_bv, ())
                                                              m_q ⟨mrk', mstk', mclr', sstk', mcl',
                                                                mcf', hb', hblk', hsstk', hm_q,
                                                                fun h => by cases h⟩
                                                        · rintro J8 hJ8
                                                          ml_ld c0_load_arena_mrk (s := st_i)
                                                            (i := ov.setWidth 64) hov_mrk_l hm_i
                                                          ml_lets; ml_jnz; refine ⟨fun hpois => ?_,
                                                            fun hnpois => ?_⟩
                                                          · ml_lets; exact hJ8 () m_i ⟨mrk_i,
                                                              mstk_i, mclr_i, sstk_i, mcl_i, mcf_i,
                                                              hb_i, hblk_i, hsstk_i, hno8', hm_i⟩
                                                          · c0_cond hnpois
                                                            ml_lets; apply wp_call_of_spec
                                                            apply hMl
                                                            have hno8_ml := shrinkOkInv_lvl_lt_no8
                                                              (fun w hw h8 => (h8_i w hw h8).1)
                                                              hlov_lt
                                                            have hmem_ot2 := hot_mem
                                                            rw [hrsn_eq] at hmem_ot2
                                                            have hot_vals :
                                                                st_i.vals[ot.toNat]?.getD 0#8 =
                                                                0xFF#8 := by
                                                              dsimp only [st_i, shrinkBlkSt]
                                                              rcases hall_q ot.toNat hmem_ot2 with
                                                                hEq | ⟨kv, hkv_lt, hkv_eq⟩
                                                              · exact absurd (BitVec.eq_of_toNat_eq
                                                                  (by rw [← huip_in_eq', hEq]))
                                                                  hot_ne
                                                              · exact (hcore.vals_false_iff _
                                                                  hot_lt).mpr
                                                                  ⟨kv, by omega, hkv_eq⟩
                                                            refine ⟨c, F0, st_i, keep0, R, rfl,
                                                              hst_i_core, hb_i.min_inv, hot_lt,
                                                              hot_vals, ?_, hm_i,
                                                              fun _ mrk_ml mstk_ml mclr_ml mcl_ml
                                                                mcf_ml m_ml hlen_ml hmono_ml
                                                                hbit8_ml hmin_ml hrem_ml hm_ml =>
                                                              ?_⟩
                                                            · intro w hw hle
                                                              exact hno8_ml w hw hle
                                                            · ml_lets; dsimp only; ml_jnz
                                                              refine ⟨fun hml_ok => ?_,
                                                                fun hml_fail => ?_⟩
                                                              · ml_lets; apply wp_call_of_spec
                                                                apply hMm
                                                                have hmin2_ml := (hrem_ml hml_ok).2
                                                                change PlainMinMarkInv c F0
                                                                  (plainMinMarkState c _
                                                                    (ot.toNat / 2) 2#8) keep0
                                                                  at hmin2_ml
                                                                rw [← hov_nat] at hmin2_ml
                                                                refine shrink_ml_ok_spec hcore hb_i
                                                                  hov_lt hno8' hlen_ml hmono_ml
                                                                  hbit8_ml hmin_ml hmin2_ml hblk_lt
                                                                  hblk_i hsstk_i h8_i hcnt_i
                                                                  hm_ml fun mrk' mstk' mclr' sstk'
                                                                    mcl' mcf' m_2 hb2 hmono2_all
                                                                    hbit8_all hov_2 hblk2 hsstk2
                                                                    h8_2 hcnt2 hm_2 => by
                                                                  have hm8_eq : ∀ w < c.mv,
                                                                      (mrk_i[w]?.getD 0#8 &&& 8#8)
                                                                      ≠ 0#8 →
                                                                      (mrk'[w]?.getD 0#8 &&& 8#8)
                                                                      ≠ 0#8 := fun w hw h => by
                                                                    rwa [hbit8_all w hw]
                                                                  exact hJ7 (false, ()) m_2
                                                                    ⟨rfl, by omega, mrk', mstk',
                                                                      mclr', sstk', mcl', mcf', hb2,
                                                                      hblk2, hsstk2, hm_2, hop_i,
                                                                      hopl_i, h8_2, hcnt2,
                                                                      hcov_pref_step hmono2_all
                                                                        hm8_eq (Or.inr (Or.inr
                                                                          (Or.inl (by
                                                                            rwa [← hov_nat]))))⟩
                                                              · ml_lets
                                                                obtain ⟨hb_ml, hblk_ml, hsstk_ml,
                                                                  hno8_mlv⟩ := shrink_ml_fail_base
                                                                    hb_i hov_lt hno8' hlen_ml
                                                                    hmono_ml hbit8_ml hmin_ml
                                                                    hblk_lt hblk_i hsstk_i
                                                                exact hJ8 () m_ml ⟨mrk_ml, mstk_ml,
                                                                  mclr_ml, sstk_i, mcl_ml, mcf_ml,
                                                                  hb_ml, hblk_ml, hsstk_ml,
                                                                  hno8_mlv, hm_ml⟩
                                                      · c0_cond hhas2
                                                        have h2' : (mrk_i[ot.toNat / 2]?.getD 0#8
                                                            &&& 2#8) ≠ 0#8 := by
                                                          rw [getElem?_getD_of_getElem 0#8
                                                            (rfl : mrk_i = st_i.mrk) hov_nat.symm]
                                                          exact hhas2
                                                        ml_lets
                                                        exact hJ7 (false, ()) m_i
                                                          ⟨rfl, by omega, mrk_i, mstk_i, mclr_i,
                                                            sstk_i, mcl_i, mcf_i, hb_i, hblk_i,
                                                            hsstk_i, hm_i, hop_i, hopl_i, h8_i,
                                                            hcnt_i, hcov_pref_step (fun _ _ h => h)
                                                              (fun _ _ h => h)
                                                              (Or.inr (Or.inr (Or.inl h2')))⟩
                                                  · c0_cond hge_blvl
                                                    dsimp only [st_i, shrinkBlkSt] at hge_blvl
                                                    have hlov_ge : blvl.toNat ≤
                                                        (s.lvl[ot.toNat / 2]?.getD 0#32).toNat := by
                                                      rw [getElem?_getD_of_getElem 0#32
                                                        (hj := by rw [hlen0.lvl_len]; exact hov_lt)
                                                        rfl hov_nat.symm]
                                                      omega
                                                    ml_lets; ml_jnz
                                                    refine ⟨fun hsl_lt => ?_, fun hsl_ge => ?_⟩
                                                    · c0_cond hsl_lt
                                                      have hcmv := c.hmv
                                                      have hsl_lt' : slen_i.toNat < c.mv := by omega
                                                      ml_ld c0_load_arena_mrk (s := st_i)
                                                        (i := ov.setWidth 64) hov_mrk_l hm_i
                                                      ml_lets
                                                      ml_st m_s1, hm_s1 := c0_store_arena_mrk
                                                        (s := st_i) (i := ov.setWidth 64) _
                                                        hov_mrk_l hm_i
                                                      let mrk2 := mrk_i.set ov.toNat
                                                        (mrk_i[ov.toNat]?.getD 0#8 ||| 8#8)
                                                      have hm_s1' := hm_s1
                                                      dsimp only [st_i, shrinkBlkSt] at hm_s1'
                                                      simp only [bv_c0_zext32_64, Arg.val_var,
                                                        bv8_or8_c0] at hm_s1'
                                                      have hm_1 : (PlainMem c (shrinkBlkSt s s.tmp
                                                          mrk2 mstk_i mclr_i mcl_i mcf_i sstk_i) ⋆
                                                          R) m_s1 := by
                                                        dsimp only [shrinkBlkSt, mrk2]
                                                        rw [List.getElem?_eq_getElem
                                                          (by rw [hb_i.mrk_len]; exact hov_lt),
                                                          Option.getD_some]
                                                        exact hm_s1'
                                                      have hsl_stk : slen_i.toNat < (shrinkBlkSt s
                                                          s.tmp mrk2 mstk_i mclr_i mcl_i mcf_i
                                                          sstk_i).heur.shrink_stk.length := by
                                                        dsimp only [shrinkBlkSt]
                                                        rw [hb_i.sstk_len]; exact hsl_lt'
                                                      ml_st m_s2, hm_s2 :=
                                                        c0_store_arena_shrink_stk (s := shrinkBlkSt
                                                          s s.tmp mrk2 mstk_i mclr_i mcl_i mcf_i
                                                          sstk_i) (i := slen_i) ov hsl_stk hm_1
                                                      let sstk2 := sstk_i.set slen_i.toNat ov
                                                      have hm_2 : (PlainMem c (shrinkBlkSt s s.tmp
                                                          mrk2 mstk_i mclr_i mcl_i mcf_i sstk2) ⋆
                                                          R) m_s2 := by
                                                        dsimp only [shrinkBlkSt, sstk2]
                                                          at hm_s2 ⊢
                                                        exact hm_s2
                                                      have hmem_ot := hot_mem
                                                      rw [hrsn_eq] at hmem_ot
                                                      rcases hall_q ot.toNat hmem_ot with
                                                        hEq | ⟨kot, hkot_lt, hkot_eq⟩
                                                      · exfalso; apply hot_ne
                                                        exact BitVec.eq_of_toNat_eq (by
                                                          rw [← huip_in_eq', hEq])
                                                      · have huip_lvl' :
                                                            (s.lvl[(s.trl[t_in.toNat]?.getD 0#32
                                                              ).toNat / 2]?.getD 0#32).toNat =
                                                            blvl.toNat := by
                                                          rw [huip_in_eq']
                                                          exact (h8_c _ (by omega) huip_in_8).1
                                                        obtain ⟨hb2, hblk2, hsstk2, h8_2, hcnt2,
                                                          hop2, hopl2, h8_new⟩ :=
                                                          shrink_step_pre_push8 hcore hb_i hblk_lt
                                                            hblk_i hsstk_i h8_i hcnt_i hop_i hopl_i
                                                            hsl_lt' hot_lt ht_te huip_lvl' hkot_lt
                                                            hkot_eq (by omega : kot ≤ t_next.toNat)
                                                            hlov_ge
                                                        have hop1' : (open_i + 1).toNat =
                                                            open_i.toNat + 1 :=
                                                          min_bv64_add1 (by omega)
                                                        have hsl1' : (slen_i + 1).toNat =
                                                            slen_i.toNat + 1 :=
                                                          min_bv64_add1 (by omega)
                                                        obtain ⟨hm2_eq, hm8_eq⟩ :=
                                                          shrink_set_bit8_monos hb_i.mrk_len hov_lt
                                                        ml_lets; exact hJ6 (open_i + 1, slen_i + 1,
                                                          false, ()) m_s2 ⟨rfl, by omega, mrk2,
                                                            mstk_i, mclr_i, sstk2, mcl_i, mcf_i,
                                                            by rw [hsl1']; exact hb2, hblk2,
                                                            by rw [hsl1']; exact hsstk2, hm_2,
                                                            by rw [hop1']; exact hop2,
                                                            by rw [hop1', hsl1']; exact hopl2, h8_2,
                                                            by rw [hop1']; exact hcnt2,
                                                            hcov_pref_step hm2_eq hm8_eq
                                                              (Or.inr (Or.inr (Or.inr h8_new)))⟩
                                                    · ml_lets
                                                      exact hJcl (open_i, slen_i, true, i_bv, ())
                                                        m_i ⟨mrk_i, mstk_i, mclr_i, sstk_i, mcl_i,
                                                          mcf_i, hb_i, hblk_i, hsstk_i, hm_i,
                                                          fun h => by cases h⟩
                                              · c0_cond hhas8
                                                have h8' : (mrk_i[ot.toNat / 2]?.getD 0#8 &&&
                                                    8#8) ≠ 0#8 := by
                                                  rw [getElem?_getD_of_getElem 0#8
                                                    (rfl : mrk_i = st_i.mrk) hov_nat.symm]
                                                  exact hhas8
                                                ml_lets
                                                exact hJ5 (open_i, slen_i, false, ()) m_i
                                                  ⟨rfl, by omega, mrk_i, mstk_i, mclr_i, sstk_i,
                                                    mcl_i, mcf_i, hb_i, hblk_i, hsstk_i, hm_i,
                                                    hop_i, hopl_i, h8_i, hcnt_i,
                                                    hcov_pref_step (fun _ _ h => h)
                                                      (fun _ _ h => h)
                                                      (Or.inr (Or.inr (Or.inr h8')))⟩
                                            · c0_cond hlz
                                              dsimp only [st_i, shrinkBlkSt] at hlz
                                              have h0v : (0 : BitVec 32).toNat = 0 := rfl
                                              rw [h0v] at hlz
                                              have hlz' : (s.lvl[ot.toNat / 2]?.getD 0#32).toNat =
                                                  0 := by
                                                rw [getElem?_getD_of_getElem 0#32
                                                  (hj := by rw [hlen0.lvl_len]; exact hov_lt) rfl
                                                  hov_nat.symm]
                                                omega
                                              ml_lets
                                              exact hJ5 (open_i, slen_i, false, ()) m_i
                                                ⟨rfl, by omega, mrk_i, mstk_i, mclr_i, sstk_i,
                                                  mcl_i, mcf_i, hb_i, hblk_i, hsstk_i, hm_i, hop_i,
                                                  hopl_i, h8_i, hcnt_i,
                                                  hcov_pref_step (fun _ _ h => h)
                                                    (fun _ _ h => h) (Or.inr (Or.inl hlz'))⟩
                                          · exfalso; change (ov.setWidth 64).ult
                                              (BitVec.ofNat 64 c.mv) = false at hov_oob
                                            c0_cond hov_oob; have hcmv := c.hmv; omega
                                        · change (ot != uip_in) = false at hot_eq_u
                                          c0_cond hot_eq_u; ml_lets
                                          exact hJ5 (open_i, slen_i, false, ()) m_i ⟨rfl, by omega,
                                            mrk_i, mstk_i, mclr_i, sstk_i, mcl_i, mcf_i, hb_i,
                                            hblk_i, hsstk_i, hm_i, hop_i, hopl_i, h8_i, hcnt_i,
                                            hcov_pref_step (fun _ _ h => h) (fun _ _ h => h)
                                              (Or.inl (by rw [huip_in_eq', hot_eq_u]))⟩
                                    · change i_bv.ult csz = false at hidone; c0_cond hidone
                                      have hic : i_bv.toNat = csz.toNat := by omega
                                      ml_lets; refine hJcl (open_i, slen_i, false, i_bv, ()) m_i
                                        ⟨mrk_i, mstk_i, mclr_i, sstk_i, mcl_i, mcf_i, hb_i, hblk_i,
                                          hsstk_i, hm_i, fun _ => ⟨hop_i, hopl_i, h8_i, hcnt_i,
                                            shrink_clause_loop_done hcore ht_te hrsn_ne' hcl_b'
                                              fun j hj => ?_⟩⟩
                                      have hqj := hpref_i j (by
                                        rw [hic, hcsz_nat, hrsn_eq]; exact hj)
                                      rwa [hrsn_eq] at hqj
                                  · intro J4 hJ4; ml_lets
                                    exact hJ4 csz.toNat (open_c, slen_c, 0#32, ()) m_c ⟨rfl,
                                      Nat.zero_le _, mrk_c, mstk_c, mclr_c, sstk_c, mcl_c, mcf_c,
                                      hb_c, hblk_c, hsstk_c, hm_c, hop_ge2, hop_le, h8_pre,
                                      hcnt_pre, fun _ hk => by simp at hk⟩
            · intro J_in hJ_in
              refine wp_loop_group (ts := [i64]) (fun ni (t', ()) m_in =>
                  m_in = m_c ∧ ni = (if s.trail_end ≤ t'.toNat then 0 else t'.toNat) ∧
                  t'.toNat ≤ t_c.toNat ∧
                  ∀ j, t'.toNat < j → j < s.trail_end → j ≤ t_c.toNat →
                    (mrk_c[(s.trl[j]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 8#8) = 0#8) ?_ ?_
              · rintro Ji ni ⟨t', ⟨⟩⟩ m_in hJi ⟨hm_in, rfl, htle, hgap⟩
                subst m_in
                rw [Blocks.get_here, wp]; simp only [Arg.val_imm]
                refine ⟨fun _ => ?_, fun hf => by cases hf⟩
                ml_ld load_arena_trail_end hm_c
                ml_lets; ml_jnz; refine ⟨fun hge => ?_, fun hlt => ?_⟩
                · ml_lets; exact hJ_in (true, uip_c, t', ()) m_c ⟨rfl, fun h => by cases h⟩
                · c0_cond hlt
                  have ht_te : t'.toNat < s.trail_end := by
                    dsimp only [st_c, shrinkBlkSt] at hlt
                    have := hlen0.trail_end_le; omega
                  have htr_ls : t'.toNat < s.trl.length := by
                    rw [hlen0.trl_len]; exact lt_of_lt_of_le ht_te hlen0.trail_end_le
                  ml_ld c0_load_arena_trl (s := st_c) (i := t')
                    (by dsimp only [st_c, shrinkBlkSt]; exact htr_ls) hm_c
                  let lit := s.trl[t'.toNat]'htr_ls
                  have hlit_lt : lit.toNat < 2 * c.mv := by
                    have := hcore.trail_lits_lt t'.toNat ht_te
                    dsimp only [lit]
                    rwa [List.getElem?_eq_getElem htr_ls, Option.getD_some] at this
                  have hv_lt : (lit >>> 1).toNat < c.mv := by rw [bv32_lshr_1]; omega
                  have hv_mrk_l : ((lit >>> 1).setWidth 64).toNat < st_c.mrk.length := by
                    dsimp only [st_c, shrinkBlkSt]
                    rw [hb_c.mrk_len, bv_c0_zext32_64]; exact hv_lt
                  ml_ld c0_load_arena_mrk (s := st_c) (i := (lit >>> 1).setWidth 64) hv_mrk_l hm_c
                  ml_lets; ml_jnz; refine ⟨fun hnz => ?_, fun hz => ?_⟩
                  · c0_cond hnz
                    have h8nz : (mrk_c[lit.toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8 := by
                      rw [getElem?_getD_of_getElem 0#8 (rfl : mrk_c = st_c.mrk)
                        (bv32_lshr_1 lit).symm]
                      exact hnz
                    rw [wp, hnfail]
                    refine hJ_in (false, lit, t', ()) m_c ⟨rfl, fun _ => ⟨ht_te, htle,
                      by dsimp only [lit]; rw [List.getElem?_eq_getElem htr_ls, Option.getD_some],
                      h8nz, hgap⟩⟩
                  · c0_cond hz
                    have h8z : (mrk_c[lit.toNat / 2]?.getD 0#8 &&& 8#8) = 0#8 := by
                      rw [getElem?_getD_of_getElem 0#8 (rfl : mrk_c = st_c.mrk)
                        (bv32_lshr_1 lit).symm]
                      exact hz
                    ml_lets; ml_jnz; refine ⟨fun ht0 => ?_, fun ht_ne0 => ?_⟩
                    · ml_lets; exact hJ_in (true, uip_c, t', ()) m_c ⟨rfl, fun h => by cases h⟩
                    · c0_cond ht_ne0
                      have ht_pos : 1 ≤ t'.toNat := bv64_pos_of_ne0 ht_ne0
                      have htm1 : (t' - 1).toNat = t'.toNat - 1 := min_bv64_sub1 ht_pos
                      have hdec_i : (if s.trail_end ≤ (t' - 1).toNat then 0 else
                          (t' - 1).toNat) < if s.trail_end ≤ t'.toNat then 0 else t'.toNat := by
                        simp only [show ¬ s.trail_end ≤ t'.toNat by omega,
                          show ¬ s.trail_end ≤ (t' - 1).toNat by omega, ↓reduceIte]; omega
                      ml_lets
                      refine hJi (if s.trail_end ≤ (t' - 1).toNat then 0 else (t' - 1).toNat)
                        (t' - 1, ()) m_c hdec_i ⟨rfl, rfl, by omega, fun j hj1 hj2 hj3 => ?_⟩
                      by_cases hjt : j = t'.toNat
                      · subst j
                        rwa [List.getElem?_eq_getElem htr_ls, Option.getD_some]
                      · exact hgap j (by omega) hj2 hj3
              · intro Ji hJi; ml_lets; exact hJi (if s.trail_end ≤ t_c.toNat then 0 else t_c.toNat)
                  (t_c, ()) m_c ⟨rfl, rfl, le_refl _, fun _ h1 _ h2 => by omega⟩
        · exact fun Jm hJm => by
            ml_lets
            have hop0 : (end_b - beg).toNat = end_b.toNat - beg.toNat :=
              min_bv64_sub (le_of_lt hbeg_end)
            refine hJm (if (false : Bool) = true then 0 else min max_tr.toNat s.trail_end + 1)
              (end_b - beg, slen_bv, false, 0xFFFFFFFF#32, max_tr, ()) m1
              ⟨mrk1, s.min_stk, s.min_clr, sstk1, s.min_clr_len, s.min_clr_full, rfl, hb1,
                hblk_k, hsstk_k, hm1, fun _ => ⟨by omega, by omega, fun w hw hw8 => ?_,
                  by rw [hop0, ← hsl_eq]; exact hcnt_k⟩⟩
            obtain ⟨j, hj1, hj2, hjv⟩ := h8_k w hw hw8
            have hsp := hblk_spec j hj1 hj2
            obtain ⟨idx, hidx_te, hidx_eq⟩ := (hcore.vals_false_iff _ hsp.1).mp hsp.2.1
            have hidx_v : (s.trl[idx]?.getD 0#32).toNat / 2 = w := by
              rw [hidx_eq, xor1_div2, hjv]
            have htp := hcore.trail_pos_inv idx hidx_te
            rw [hidx_v] at htp
            exact ⟨by rw [← hjv]; exact hsp.2.2.1, idx, hidx_te, hidx_v,
              Or.inl (by rw [← htp, ← hjv]; exact hsp.2.2.2)⟩
  · intro J1 hJ1; ml_lets; exact hJ1 (end_b.toNat - beg.toNat) (0#64, beg, ()) m ⟨s.mrk,
      s.heur.shrink_stk, rfl, le_refl _, le_of_lt hbeg_end, by simp, ⟨hlen0.mrk_len,
      hlen0.min_stk_len, hlen0.min_clr_len_arr, hlen0.min_clr_len_le, hlen0.heur_ok.shrink_stk_len,
      Nat.zero_le _, hmin0, fun _ _ h => h, fun w hw h8 => absurd (hno8_0 w hw) h8, fun _ h => by
      simp at h⟩, fun _ h1 h2 => by omega, fun _ h => by simp at h, fun w hw h8 =>
      absurd (hno8_0 w hw) h8, ⟨by
        rw [trailCount8_zero_of_all_zero (lim := s.trail_end) (fun i hi => by
          have := hcore.trail_lits_lt i hi; omega) hno8_0 _ (Nat.min_le_right _ _)]
        exact Nat.zero_le _, hm⟩⟩

end LeanQbe.T.Examples.Kissat.Plain
