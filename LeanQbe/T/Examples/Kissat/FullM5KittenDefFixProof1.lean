module

public import LeanQbe.T.Examples.Kissat.FullM5KittenDefFix
public import LeanQbe.T.Examples.Kissat.FullKittenLemmas1
public import LeanQbe.T.Examples.Kissat.FullKittenLemmas2
public import LeanQbe.T.Examples.Kissat.FullKittenLemmas6

/-!
# Kissat `M5` Wave 0 (`RC-08`) Kitten `Func.wp` Proofs (`Part 1`)

Proves parametric `(Γ : Env)` `Func.wp` contracts against canonical `Full.fullKitten*Spec` for:
1. `full_kitten_add_clause_m5_wp` (`Full.fullKittenAddClauseSpec`, clean `nu >= 256u` rejection)
2. `full_kitten_build_failing_m5_wp` (`Full.fullKittenBuildFailingSpec`, clears `KM_CORE` first)
3. `full_kitten_core_m5_wp` (`Full.fullKittenCoreSpec`, `INCONS`-first `KM_CORE` clear + DAG close)
4. `full_kitten_solve_m5_wp` (`Full.fullKittenSolveSpec`, saturating `TICK_LIM` + strict `<`)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM5KittenDefFix

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

open scoped KittenMemTactics KittenMemATactics KittenProjTactics

local macro "c0_hcall" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

/-! ## 1. `full_kitten_add_clause_m5_wp` (`Full.fullKittenAddClauseSpec`) -/

/-- Parametric `Func.wp` proof for `full_kitten_add_clause_m5` (`nu >= 256u` returns `false`). -/
theorem full_kitten_add_clause_m5_wp (Γ : Env)
    (hWatch : ∀ args m Q X, fullKittenWatchSpec args m Q X →
      Γ "full_kitten_watch" [i64, i32, i32, i32] [] args m Q X) :
    ∀ args m Q X, fullKittenAddClauseSpec args m Q X →
      Func.wp Γ full_kitten_add_clause_m5_body args m Q X := by
  rintro ⟨hPtr, cid, litsPtr, sz, ⟨⟩⟩ m Q X ⟨c, s, scr, xs, R, rfl, hlen, hscr_buf,
    hinv_s, hsync, hlvl0, hte0, heq_nc, hsz_xs, hsz_max, hxlits, hm, hQ⟩
  rcases hinv_s with ⟨hscr_ge, hscr_lt, hinv⟩
  let acap := scr.length - 8864
  let ks := kittenStateOfScratch scr
  have hsh := hinv.shapes
  have hnv := hinv.clauses.nv_le
  have hal := hinv.clauses.alen_le
  have hacap_lt : acap < 2 ^ 28 := hinv.clauses.acap_lt
  have hca_eq : ks.acap.toNat = acap := by
    rw [hinv.clauses.acap_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hscr_len : scr.length = c.scratch_cap := by
    rw [← hscr_buf]; exact hlen.scratch_ok.scratch_buf_len
  have hscr_8864 : 8864 ≤ scr.length := by unfold kMinScratchCap at hscr_ge; omega
  let kPtr := c.pScratchBuf + BitVec.ofNat 64 256 * 4
  let Rrest : Mem 64 → Prop := array (t := i32) litsPtr xs ⋆
    (array (t := i32) c.pScratchBuf (scr.take 256) ⋆ R)
  have hof_ks : KittenState.ofSlab (scr.drop 256) = ks := rfl
  have hmA : (KittenMemA kPtr acap ks ⋆
      (array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ Rrest)) m :=
    fullAddClause_mem_to_ka hscr_8864 hsh hof_ks hm
  clear hm
  have hreorg : ∀ {ks' : KittenState} {m' : Mem 64} (hsh' : ks'.ShapesOk acap),
      (KittenMemA kPtr acap ks' ⋆
        (array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ Rrest)) m' →
      let scr' := scr.take 256 ++ ks'.toSlab
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      scr'.length = c.scratch_cap ∧ (∀ i < kBase, scr'[i]? = scr[i]?) ∧
      (array64 (c.hdr + 32) (Full.hdrTailWords c s') ⋆ array (t := i32) c.pScratchBuf scr' ⋆
        array (t := i32) litsPtr xs ⋆ R) m' := by
    intro ks' m' hsh' hm' scr' s'
    have htk : (scr.take 256).length = 256 := List.length_take_of_le (by omega)
    have hlen' : scr'.length = c.scratch_cap := by
      simp only [scr', List.length_append, htk, KittenState.toSlab_length hsh']; omega
    have hpre : ∀ i < kBase, scr'[i]? = scr[i]? := by
      intro i hi
      rw [List.getElem?_append_left (by unfold kBase at hi; omega),
        List.getElem?_take_of_lt (by unfold kBase at hi; omega)]
    exact ⟨hlen', hpre, fullAddClause_ka_to_mem (by omega) hsh' hm'⟩
  have hscr_orig : scr.take 256 ++ ks.toSlab = scr := by
    unfold ks kittenStateOfScratch
    rw [KittenState.toSlab_ofSlab (by simp; omega), List.take_append_drop]
  have hof_slab : ∀ {ks' : KittenState} (hsh' : ks'.ShapesOk acap),
      kittenStateOfScratch (scr.take 256 ++ ks'.toSlab) = ks' := by
    intro ks' hsh'
    unfold kittenStateOfScratch
    rw [slab_drop_exact _ ks'.toSlab (by simp; omega)]
    exact KittenState.ofSlab_toSlab hsh'
  have hret_false : Q (false, ()) m := by
    have hmF := hreorg hsh hmA
    have hinv_fin : KittenScratchInv scr := ⟨hscr_ge, hscr_lt, hinv⟩
    rw [hscr_orig] at hmF
    exact hQ false scr m hscr_len (fun _ _ => rfl) hinv_fin hsync hlvl0 hte0 rfl heq_nc
      rfl rfl rfl (fun _ => rfl) (fun h => by cases h) hmF.2.2
  c0_hsplit
  · c0_hsteps!; exact hret_false
  · c0_hsplit
    · c0_hsteps!; exact hret_false
    · have hal_ks : ks.alen.toNat ≤ ks.acap.toNat := by rw [hca_eq]; exact hal
      have hcap_lt : ks.acap.toNat < 2 ^ 28 := by rw [hca_eq]; exact hacap_lt
      have hnc_lt : ks.nc.toNat < kMaxOrig := by unfold kMaxOrig; bv_omega
      have hnc_896 : ks.nc.toNat < 896 := by unfold kMaxOrig at hnc_lt; omega
      have hnc_wrap : ks.nc.toNat < 2 ^ 28 := by omega
      have hoff_fit : ks.alen.toNat + sz.toNat ≤ ks.acap.toNat := by bv_omega
      -- Guard `if (sz == 1u && k[KH_NUNITS] >= 256u) { return false; }`
      c0_hsteps_nogrp
      refine wp_join0 (fun m0 => m0 = m ∧ (sz = 1#32 → ks.nunits.toNat < 256)) ?_ ?_
      · intro Jg m0 ⟨hm0, hsz1_nu⟩; subst hm0
        c0_hsplit
        · c0_hsteps!
          · have hin_eq : (ks.incons == 0xFFFFFFFF#32) = true := beq_iff_eq.mpr ‹_›
            have hpres := addClause_empty_preserves (cid := cid) hinv hsync hlvl0 hte0 heq_nc hnc_lt
            let st0 := ((ks.putArr .clOff ks.nc.toNat ks.alen).putArr .clMeta ks.nc.toNat
              0#32).putArr .clAux ks.nc.toNat cid
            let st1 := if ks.incons == 0xFFFFFFFF#32 then st0.putHdr .incons ks.nc else st0
            let ks' := (st1.putHdr .nc (ks.nc + 1#32)).putHdr .orig_nc (ks.nc + 1#32)
            have hk_nv : ks'.nv = ks.nv := by dsimp only [ks', st1, st0]; split <;> kp_field
            have hk_an : ks'.ante = ks.ante := by dsimp only [ks', st1, st0]; split <;> kp_field
            have hk_na : ks'.nassump = ks.nassump := by
              dsimp only [ks', st1, st0]; split <;> kp_field
            have hm_ks' : (KittenMemA kPtr acap ks' ⋆
                (array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ Rrest)) m := by
              refine Eq.mp (congrArg (fun x => (KittenMemA kPtr acap x ⋆ _) _) ?_) hm
              dsimp only [ks', st1, st0]; simp only [hin_eq, ite_true]; rfl
            have hsh' := hpres.1.shapes
            have hmF := hreorg hsh' hm_ks'
            have hinv' : KittenScratchInv (scr.take 256 ++ ks'.toSlab) := by
              refine ⟨by rw [hmF.1]; omega, by rw [hmF.1]; exact c.hscr, ?_⟩
              rw [hof_slab hsh', show (scr.take 256 ++ ks'.toSlab).length - 8864 = acap by
                rw [hmF.1]; omega]
              exact hpres.1
            have hsz0 : sz = 0#32 := ‹_›
            have htk0 : ((xs.take sz.toNat).map BitVec.toNat) = [] := by rw [hsz0]; simp
            have horig' : kittenOrigClausesS (scr.take 256 ++ ks'.toSlab) =
                kittenOrigClausesS scr ++ [(xs.take sz.toNat).map BitVec.toNat] := by
              unfold kittenOrigClausesS; rw [hof_slab hsh', htk0]; exact hpres.2.2.2.2.2.2.2.2.1
            exact hQ true _ _ hmF.1 hmF.2.1 hinv'
              (by rw [hof_slab hsh']; exact hpres.2.1) (by rw [hof_slab hsh']; exact hpres.2.2.1)
              (by rw [hof_slab hsh']; exact hpres.2.2.2.1)
              (by rw [hof_slab hsh']; exact hk_nv)
              (by rw [hof_slab hsh']; exact hpres.2.2.2.2.1)
              (by rw [hof_slab hsh']; exact hk_an)
              (by rw [hof_slab hsh']; exact hk_na)
              (by unfold kittenAssumpLitsS; rw [hof_slab hsh']; exact hpres.2.2.2.2.2.2.2.2.2.1)
              (fun h => by cases h)
              (fun _ => ⟨by rw [hof_slab hsh']; exact hpres.2.2.2.2.2.1,
                by rw [hof_slab hsh']; exact hpres.2.2.2.2.2.2.1,
                by rw [hof_slab hsh']; exact hpres.2.2.2.2.2.2.2.2.2.2,
                by rw [hof_slab hsh', hsz0]; exact hpres.2.2.2.2.2.2.2.1, horig',
                fun _ _ => by
                  rw [hof_slab hsh']
                  have hwb : ks'.wblit = ks.wblit := by
                    dsimp only [ks', st1, st0]; split <;> kp_field
                  rw [hwb],
                fun h2 => by rw [hsz0] at h2; simp at h2⟩)
              hmF.2.2
          · have hin_ne : (ks.incons == 0xFFFFFFFF#32) = false := beq_false_of_ne ‹_›
            have hpres := addClause_empty_preserves (cid := cid) hinv hsync hlvl0 hte0 heq_nc hnc_lt
            let st0 := ((ks.putArr .clOff ks.nc.toNat ks.alen).putArr .clMeta ks.nc.toNat
              0#32).putArr .clAux ks.nc.toNat cid
            let st1 := if ks.incons == 0xFFFFFFFF#32 then st0.putHdr .incons ks.nc else st0
            let ks' := (st1.putHdr .nc (ks.nc + 1#32)).putHdr .orig_nc (ks.nc + 1#32)
            have hk_nv : ks'.nv = ks.nv := by dsimp only [ks', st1, st0]; split <;> kp_field
            have hk_an : ks'.ante = ks.ante := by dsimp only [ks', st1, st0]; split <;> kp_field
            have hk_na : ks'.nassump = ks.nassump := by
              dsimp only [ks', st1, st0]; split <;> kp_field
            have hm_ks' : (KittenMemA kPtr acap ks' ⋆
                (array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ Rrest)) m := by
              refine Eq.mp (congrArg (fun x => (KittenMemA kPtr acap x ⋆ _) _) ?_) hm
              dsimp only [ks', st1, st0]; simp only [hin_ne, Bool.false_eq_true, ite_false]; rfl
            have hsh' := hpres.1.shapes
            have hmF := hreorg hsh' hm_ks'
            have hinv' : KittenScratchInv (scr.take 256 ++ ks'.toSlab) := by
              refine ⟨by rw [hmF.1]; omega, by rw [hmF.1]; exact c.hscr, ?_⟩
              rw [hof_slab hsh', show (scr.take 256 ++ ks'.toSlab).length - 8864 = acap by
                rw [hmF.1]; omega]
              exact hpres.1
            have hsz0 : sz = 0#32 := ‹_›
            have htk0 : ((xs.take sz.toNat).map BitVec.toNat) = [] := by rw [hsz0]; simp
            have horig' : kittenOrigClausesS (scr.take 256 ++ ks'.toSlab) =
                kittenOrigClausesS scr ++ [(xs.take sz.toNat).map BitVec.toNat] := by
              unfold kittenOrigClausesS; rw [hof_slab hsh', htk0]; exact hpres.2.2.2.2.2.2.2.2.1
            exact hQ true _ _ hmF.1 hmF.2.1 hinv'
              (by rw [hof_slab hsh']; exact hpres.2.1) (by rw [hof_slab hsh']; exact hpres.2.2.1)
              (by rw [hof_slab hsh']; exact hpres.2.2.2.1)
              (by rw [hof_slab hsh']; exact hk_nv)
              (by rw [hof_slab hsh']; exact hpres.2.2.2.2.1)
              (by rw [hof_slab hsh']; exact hk_an)
              (by rw [hof_slab hsh']; exact hk_na)
              (by unfold kittenAssumpLitsS; rw [hof_slab hsh']; exact hpres.2.2.2.2.2.2.2.2.2.1)
              (fun h => by cases h)
              (fun _ => ⟨by rw [hof_slab hsh']; exact hpres.2.2.2.2.2.1,
                by rw [hof_slab hsh']; exact hpres.2.2.2.2.2.2.1,
                by rw [hof_slab hsh']; exact hpres.2.2.2.2.2.2.2.2.2.2,
                by rw [hof_slab hsh', hsz0]; exact hpres.2.2.2.2.2.2.2.1, horig',
                fun _ _ => by
                  rw [hof_slab hsh']
                  have hwb : ks'.wblit = ks.wblit := by
                    dsimp only [ks', st1, st0]; split <;> kp_field
                  rw [hwb],
                fun h2 => by rw [hsz0] at h2; simp at h2⟩)
              hmF.2.2
        · have hsz_pos : 1 ≤ sz.toNat := by
            have hne : sz ≠ 0#32 := ‹_›
            exact Nat.pos_of_ne_zero fun hz => hne (BitVec.eq_of_toNat_eq hz)
          refine wp_while_state1 (fun p : BitVec 32 × List (BitVec 32) => p.1)
            (fun p => sz.toNat - p.1.toNat)
            (fun p m' => p.1.toNat ≤ sz.toNat ∧ p.2.length = acap ∧
              (∀ j < ks.alen.toNat, p.2[j]? = ks.arena[j]?) ∧
              (∀ j < p.1.toNat, p.2[ks.alen.toNat + j]? = xs[j]?) ∧
              (KittenMemA kPtr acap { ks with arena := p.2 } ⋆
                (array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
                  (array (t := i32) litsPtr xs ⋆
                    (array (t := i32) c.pScratchBuf (scr.take 256) ⋆ R)))) m')
            ?_ ?_
          · intro J hJ
            exact wp_jump_state (proj := fun p : BitVec 32 × List (BitVec 32) => (p.1, ()))
              (0#32, ks.arena) rfl
              (hJ _ _ ⟨Nat.zero_le _, hsh.arena_len, fun _ _ => rfl, fun _ hj => by simp at hj,
                hmA⟩)
          · rintro J ⟨i, ar⟩ m' ⟨hi_le, har_len, har_old, har_new, hm'⟩ ih
            dsimp only at hi_le har_len har_old har_new hm' ⊢
            have hsh_ar : ({ ks with arena := ar } : KittenState).ShapesOk acap :=
              { hsh with arena_len := har_len }
            c0_hsplit
            · have hi_lt : i.toNat < sz.toNat := by bv_omega
              have hi_xs : i.toNat < xs.length := by omega
              have hsw_i : (BitVec.setWidth 64 i).toNat = i.toNat := by
                simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : i.toNat < 2 ^ 64)]
              have hi_sw : (BitVec.setWidth 64 i).toNat < xs.length := by rw [hsw_i]; exact hi_xs
              have hi_wrap : i.toNat < 2 ^ 28 := by omega
              have hoff_i_wrap : ks.alen.toNat + i.toNat < 2 ^ 28 := by omega
              have hoff_i_cap : ks.alen.toNat + i.toNat < acap := by omega
              c0_hstep; c0_hstep; c0_hstep; c0_hstep; c0_hstep
              c0_hstep; c0_hstep; c0_hstep; c0_hstep
              refine wp_store_sep
                (KittenMemATactics.store_ka_arena_off _ hoff_i_wrap hoff_i_cap hm')
                fun m hm => ?_
              c0_hsteps!
              have hi1 : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
              refine ih (i + 1#32, ar.set (ks.alen.toNat + i.toNat) (xs[i.toNat]'hi_xs)) _
                (by dsimp only; rw [hi1]; omega)
                ⟨by dsimp only; rw [hi1]; omega, by simp [har_len], ?_, ?_, ?_⟩
              · intro j hj
                rw [List.getElem?_set_ne (by omega)]; exact har_old j hj
              · intro j hj
                rw [hi1] at hj
                by_cases hji : j = i.toNat
                · subst hji
                  rw [List.getElem?_set_self (by rw [har_len]; exact hoff_i_cap),
                    List.getElem?_eq_getElem hi_xs]
                · rw [List.getElem?_set_ne (by omega)]; exact har_new j (by omega)
              · refine Eq.mp (congrArg (fun x => (KittenMemA kPtr acap x ⋆ _) m) ?_) hm
                have hxs_eq : xs[(BitVec.setWidth 64 i).toNat]'hi_sw = xs[i.toNat]'hi_xs := by
                  simp only [hsw_i]
                kstate_ext <;> (first | rfl | rw [hxs_eq])
            · have hi_eq : i.toNat = sz.toNat := by bv_omega
              rw [hi_eq] at har_new
              have hpres := addClause_nonempty_preserves (cid := cid) hinv hlvl0 hte0 heq_nc
                hnc_lt hsz_pos hsz_max hsz_xs hoff_fit har_len har_old har_new hxlits
              c0_hsplit
              · have hsz1 : sz = 1#32 := ‹_›
                have h1 : (sz == 1#32) = true := beq_iff_eq.mpr hsz1
                have hnu_lt : ks.nunits.toNat < 256 := hsz1_nu hsz1
                have hnu_wrap : ks.nunits.toNat < 2 ^ 28 := by omega
                c0_hsteps!
                let stBase : KittenState := { ks with arena := ar }
                let stMeta := (((((stBase.putHdr .alen (ks.alen + sz)).putArr .clOff
                  ks.nc.toNat ks.alen).putArr .clMeta ks.nc.toNat sz).putArr .clAux
                  ks.nc.toNat cid).putHdr .nc (ks.nc + 1#32)).putHdr .orig_nc (ks.nc + 1#32)
                let ks' := (stMeta.putArr .units stMeta.nunits.toNat ks.nc).putHdr .nunits
                  (stMeta.nunits + 1#32)
                have hm_ks' : (KittenMemA kPtr acap ks' ⋆
                    (array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ Rrest)) m := by
                  refine Eq.mp (congrArg (fun x => (KittenMemA kPtr acap x ⋆ _) _) ?_) hm
                  dsimp only [ks', stMeta, stBase]; rfl
                dsimp only at hpres
                rw [ite_eq_left ?_] at hpres
                have hsh' := hpres.1.shapes
                have hmF := hreorg hsh' hm_ks'
                have hinv' : KittenScratchInv (scr.take 256 ++ ks'.toSlab) := by
                  refine ⟨by rw [hmF.1]; omega, by rw [hmF.1]; exact c.hscr, ?_⟩
                  rw [hof_slab hsh', show (scr.take 256 ++ ks'.toSlab).length - 8864 = acap by
                    rw [hmF.1]; omega]
                  exact hpres.1
                have horig' : kittenOrigClausesS (scr.take 256 ++ ks'.toSlab) =
                    kittenOrigClausesS scr ++ [(xs.take sz.toNat).map BitVec.toNat] := by
                  unfold kittenOrigClausesS; rw [hof_slab hsh']; exact hpres.2.2.2.2.2.2.2.2.2.2.1
                exact hQ true _ _ hmF.1 hmF.2.1 hinv'
                  (by rw [hof_slab hsh']; exact hpres.2.1)
                  (by rw [hof_slab hsh']; exact hpres.2.2.1)
                  (by rw [hof_slab hsh']; exact hpres.2.2.2.1)
                  (by rw [hof_slab hsh']; rfl)
                  (by rw [hof_slab hsh']; exact hpres.2.2.2.2.1)
                  (by rw [hof_slab hsh']; exact hpres.2.2.2.2.2.2.1)
                  (by rw [hof_slab hsh']; exact hpres.2.2.2.2.2.2.2.1)
                  (by unfold kittenAssumpLitsS; rw [hof_slab hsh']
                      exact hpres.2.2.2.2.2.2.2.2.2.2.2.1)
                  (fun h => by cases h)
                  (fun _ => ⟨by rw [hof_slab hsh']; exact hpres.2.2.2.2.2.1,
                    by rw [hof_slab hsh']; exact hpres.2.2.2.2.2.2.2.2.1,
                    by rw [hof_slab hsh']; exact hpres.2.2.2.2.2.2.2.2.2.2.2.2,
                    by rw [hof_slab hsh']; exact hpres.2.2.2.2.2.2.2.2.2.1, horig',
                    fun _ _ => by rw [hof_slab hsh']; rfl,
                    fun h2 => by rw [hsz1] at h2; simp at h2⟩)
                  hmF.2.2
                exact ⟨h1, by kp_field; exact hnu_lt⟩
              · have hne1 : (sz == 1#32) = false := beq_false_of_ne ‹_›
                have hne1' : (sz == 1#32) ≠ true := by simp [hne1]
                have hsz2 : 2 ≤ sz.toNat := by
                  have hne : sz.toNat ≠ 1 := fun hz => (‹sz ≠ 1#32›) (BitVec.eq_of_toNat_eq hz)
                  omega
                have h0_lt : 0 < xs.length := by omega
                have h1_lt : 1 < xs.length := by omega
                c0_hsteps_nogrp
                let stBase : KittenState := { ks with arena := ar }
                let stMeta := (((((stBase.putHdr .alen (ks.alen + sz)).putArr .clOff
                  ks.nc.toNat ks.alen).putArr .clMeta ks.nc.toNat sz).putArr .clAux
                  ks.nc.toNat cid).putHdr .nc (ks.nc + 1#32)).putHdr .orig_nc (ks.nc + 1#32)
                dsimp only at hpres
                rw [ite_eq_right (fun h => hne1' h.1), ite_eq_right hne1'] at hpres
                c0_hcall hWatch
                have hsh_meta := hsh_ar.putHdr .alen (ks.alen + sz) |>.putArr .clOff ks.nc.toNat
                  ks.alen |>.putArr .clMeta ks.nc.toNat sz |>.putArr .clAux ks.nc.toNat cid
                  |>.putHdr .nc (ks.nc + 1#32) |>.putHdr .orig_nc (ks.nc + 1#32)
                have hm_nv : stMeta.nv = ks.nv := by dsimp only [stMeta, stBase]; kp_field
                have hx0 : (xs[0]'h0_lt).toNat < 2 * stMeta.nv.toNat := by
                  rw [hm_nv]; have := hxlits 0 (by omega)
                  rwa [List.getElem?_eq_getElem h0_lt, Option.getD_some] at this
                have hx1 : (xs[1]'h1_lt).toNat < 2 * stMeta.nv.toNat := by
                  rw [hm_nv]; have := hxlits 1 (by omega)
                  rwa [List.getElem?_eq_getElem h1_lt, Option.getD_some] at this
                obtain ⟨_, hm_w⟩ := kittenMemA_to_mem hm
                refine ⟨acap, stMeta, array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ Rrest,
                  hsh_meta, hacap_lt, by rw [hm_nv]; exact hnv, hnc_896, hx0, hx1, hm_w,
                  fun mW hmW => ?_⟩
                c0_hsteps!
                have hx0_bang : xs[0]! = xs[0]'h0_lt := by
                  simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h0_lt]
                have hx1_bang : xs[1]! = xs[1]'h1_lt := by
                  simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h1_lt]
                let ks' := kittenWatchStep stMeta ks.nc (xs[0]!) (xs[1]!)
                have hmW' : (KittenMem kPtr ks' ⋆
                    (array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ Rrest)) mW := by
                  refine Eq.mp (congrArg (fun x => (KittenMem kPtr x ⋆
                      (array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ Rrest)) mW) ?_) hmW
                  dsimp only [ks']; rw [hx0_bang, hx1_bang]; rfl
                have hsh' := hpres.1.shapes
                have hmF := hreorg hsh' (kittenMem_to_amem hsh' hmW')
                have hinv' : KittenScratchInv (scr.take 256 ++ ks'.toSlab) := by
                  refine ⟨by rw [hmF.1]; omega, by rw [hmF.1]; exact c.hscr, ?_⟩
                  rw [hof_slab hsh', show (scr.take 256 ++ ks'.toSlab).length - 8864 = acap by
                    rw [hmF.1]; omega]
                  exact hpres.1
                have horig' : kittenOrigClausesS (scr.take 256 ++ ks'.toSlab) =
                    kittenOrigClausesS scr ++ [(xs.take sz.toNat).map BitVec.toNat] := by
                  unfold kittenOrigClausesS; rw [hof_slab hsh']; exact hpres.2.2.2.2.2.2.2.2.2.2.1
                have hw0_n : (ks.nc <<< (1 : Nat)).toNat = 2 * ks.nc.toNat :=
                  (bv32_cid_to_w0_lt hnc_896 (Nat.le_refl _)).1
                have hw1_n : ((ks.nc <<< (1 : Nat)) ||| 1#32).toNat = 2 * ks.nc.toNat + 1 :=
                  (bv32_cid_to_w1_lt hnc_896 (Nat.le_refl _)).1
                have hwb_len : stMeta.wblit.length = 1792 := hsh_meta.wblit_len
                have hwb_old : ∀ w < 2 * ks.nc.toNat, ks'.wblit[w]? = ks.wblit[w]? := by
                  intro w hw
                  change ((stMeta.wblit.set (ks.nc <<< (1 : Nat)).toNat (xs[1]!)).set
                    ((ks.nc <<< (1 : Nat)) ||| 1#32).toNat (xs[0]!))[w]? = ks.wblit[w]?
                  rw [hw0_n, hw1_n, List.getElem?_set_ne (by omega)]
                  rw [List.getElem?_set_ne (by omega)]; rfl
                have hwb_new : ks'.wblit[2 * ks.nc.toNat]? = xs[1]? ∧
                    ks'.wblit[2 * ks.nc.toNat + 1]? = xs[0]? := by
                  constructor
                  · change ((stMeta.wblit.set (ks.nc <<< (1 : Nat)).toNat (xs[1]!)).set
                      ((ks.nc <<< (1 : Nat)) ||| 1#32).toNat (xs[0]!))[2 * ks.nc.toNat]? = xs[1]?
                    rw [hw0_n, hw1_n, List.getElem?_set_ne (by omega),
                      List.getElem?_set_self (by rw [hwb_len]; omega),
                      List.getElem?_eq_getElem h1_lt, hx1_bang]
                  · change ((stMeta.wblit.set (ks.nc <<< (1 : Nat)).toNat (xs[1]!)).set
                      ((ks.nc <<< (1 : Nat)) ||| 1#32).toNat (xs[0]!))[2 * ks.nc.toNat + 1]? =
                        xs[0]?
                    rw [hw0_n, hw1_n,
                      List.getElem?_set_self (by rw [List.length_set, hwb_len]; omega),
                      List.getElem?_eq_getElem h0_lt, hx0_bang]
                exact hQ true _ _ hmF.1 hmF.2.1 hinv'
                  (by rw [hof_slab hsh']; exact hpres.2.1)
                  (by rw [hof_slab hsh']; exact hpres.2.2.1)
                  (by rw [hof_slab hsh']; exact hpres.2.2.2.1)
                  (by rw [hof_slab hsh']; rfl)
                  (by rw [hof_slab hsh']; exact hpres.2.2.2.2.1)
                  (by rw [hof_slab hsh']; exact hpres.2.2.2.2.2.2.1)
                  (by rw [hof_slab hsh']; exact hpres.2.2.2.2.2.2.2.1)
                  (by unfold kittenAssumpLitsS; rw [hof_slab hsh']
                      exact hpres.2.2.2.2.2.2.2.2.2.2.2.1)
                  (fun h => by cases h)
                  (fun _ => ⟨by rw [hof_slab hsh']; exact hpres.2.2.2.2.2.1,
                    by rw [hof_slab hsh']; exact hpres.2.2.2.2.2.2.2.2.1,
                    by rw [hof_slab hsh']; exact hpres.2.2.2.2.2.2.2.2.2.2.2.2,
                    by rw [hof_slab hsh']; exact hpres.2.2.2.2.2.2.2.2.2.1, horig',
                    fun w hw => by rw [hof_slab hsh']; exact hwb_old w hw,
                    fun _ => by rw [hof_slab hsh']; exact hwb_new⟩)
                  hmF.2.2
      · intro Jg hJg
        c0_hsplit
        · c0_hsplit
          · c0_hsteps!; exact hret_false
          · c0_hsteps!; exact hJg m ⟨rfl, fun _ => by bv_omega⟩
        · c0_hsteps!; exact hJg m ⟨rfl, fun h => absurd h ‹_›⟩

/-! ## 2. Shared Bit & Core-Meta Helpers (`build_failing_m5` & `core_m5`) -/

private theorem fl_or2_and2_nz (x : BitVec 32) : ((x ||| 2#32) &&& 2#32) ≠ 0#32 := by
  intro h; have h1 := congrArg (fun b : BitVec 32 => b[1]) h; revert h1; simp

private theorem fl_andnot2_and2_zero (x : BitVec 32) :
    ((x &&& ~~~2#32) &&& 2#32) = 0#32 := by
  apply BitVec.eq_of_getElem_eq; intro i hi
  simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_zero]
  by_cases h1 : i = 1
  · subst h1; simp
  · have h2 : (2#32 : BitVec 32)[i] = false := by revert i hi h1; decide
    simp [h2]

private theorem trl_nodup_var_ne_m5 {acap : Nat} {ks : KittenState} (hsh : ks.ShapesOk acap)
    (hnv : ks.nv.toNat ≤ kMaxV) (hba : KittenBaseAssignOk ks)
    {i j : Nat} (hi : i < ks.trl_end.toNat) (hj : j < ks.trl_end.toNat) (hne : i ≠ j) :
    (ks.trl[i]?.getD 0#32).toNat / 2 ≠ (ks.trl[j]?.getD 0#32).toNat / 2 := by
  have hlen : ks.trl_end.toNat ≤ ks.trl.length := by
    rw [hsh.trl_len]; have := hba.trl_end_le; unfold kMaxV at hnv; omega
  have hnd := hba.trl_nodup
  unfold kittenTrailLits at hnd; rw [List.map_map] at hnd
  have hm_len : (List.map ((fun x => x / 2) ∘ BitVec.toNat)
      (ks.trl.take ks.trl_end.toNat)).length = ks.trl_end.toNat := by
    simp [List.length_take]; omega
  intro heq
  exact hne (list_nodup_getElem_inj hnd (by omega) (by omega)
    (show (List.map ((fun x => x / 2) ∘ BitVec.toNat) (ks.trl.take ks.trl_end.toNat))[i] =
        (List.map ((fun x => x / 2) ∘ BitVec.toNat) (ks.trl.take ks.trl_end.toNat))[j] by
      simp only [List.getElem_map, List.getElem_take, Function.comp_def]
      rw [List.getElem?_eq_getElem (by omega : i < ks.trl.length),
        List.getElem?_eq_getElem (by omega : j < ks.trl.length), Option.getD_some,
        Option.getD_some] at heq
      exact heq))

/-- Loop invariant for `full_kitten_build_failing_m5` (allows cleared + newly set `KM_CORE`). -/
private def FailingLoopInvM5 (ks : KittenState) (i : BitVec 32) (fls cms : List (BitVec 32)) :
    Prop :=
  i.toNat ≤ ks.trl_end.toNat ∧ fls.length = 128 ∧ cms.length = 896 ∧
  (∀ c < ks.nc.toNat,
    (cms[c]?.getD 0#32 &&& 0xFFFF#32) = (ks.clMeta[c]?.getD 0#32 &&& 0xFFFF#32) ∧
    (cms[c]?.getD 0#32 &&& kmLrn) = (ks.clMeta[c]?.getD 0#32 &&& kmLrn)) ∧
  (∀ α : Nat → Bool,
    (cnfOfClauses (((List.range ks.nc.toNat).filter fun ci =>
      (cms[ci]?.getD 0#32 &&& kmCore) != 0#32).map (kittenClauseLits ks)) ++
      unitsCnf (kittenAssumpLits ks)).Sat α →
    ∃ k < i.toNat,
      ((fls[(ks.trl[k]?.getD 0#32).toNat / 2]?.getD 0#32 &&& 2#32) ≠ 0#32) ∧
      (cnfClause [litNeg (ks.trl[k]?.getD 0#32).toNat]).Sat α)

private theorem failingStepM5_finish {acap : Nat} {ks : KittenState}
    (hsh : ks.ShapesOk acap) (hinv : ks.Inv acap) {i : BitVec 32}
    {fls fls_clr fls_j cms : List (BitVec 32)}
    (hloop : FailingLoopInvM5 ks i fls cms) (hpos : 0 < i.toNat)
    {rsn : BitVec 32} (hrsn_ne : rsn ≠ 0xFFFFFFFF#32)
    (hrsn_eq : rsn = ks.rsn[(ks.trl[i.toNat - 1]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32)
    (hclr : ∀ w < ks.nv.toNat, w ≠ (ks.trl[i.toNat - 1]?.getD 0#32).toNat / 2 →
      fls_clr[w]? = fls[w]?)
    (hkeep : ∀ w < ks.nv.toNat,
      (fls_clr[w]?.getD 0#32 &&& 2#32) ≠ 0#32 → (fls_j[w]?.getD 0#32 &&& 2#32) ≠ 0#32)
    (hmark : ∀ q < kittenClauseSize ks rsn.toNat,
      let lv := (ks.arena[kittenClauseOff ks rsn.toNat + q]?.getD 0#32).toNat / 2
      lv ≠ (ks.trl[i.toNat - 1]?.getD 0#32).toNat / 2 →
      (fls_j[lv]?.getD 0#32 &&& 2#32) ≠ 0#32)
    (hflj_len : fls_j.length = 128) :
    let cms' := cms.set rsn.toNat (cms[rsn.toNat]?.getD 0#32 ||| kmCore)
    FailingLoopInvM5 ks (i - 1#32) fls_j cms' := by
  intro cms'
  have hnv := hinv.clauses.nv_le
  have hnc := hinv.clauses.nc_le
  have hi_le := hloop.1
  have hi1_lt : i.toNat - 1 < ks.trl_end.toNat := by omega
  have hi_sub : (i - 1#32).toNat = i.toNat - 1 := by
    have := hinv.assign.trl_end_le; unfold kMaxV at hnv; bv_omega
  have hro := hinv.reasons (i.toNat - 1) hi1_lt
  dsimp only at hro
  let lit := (ks.trl[i.toNat - 1]?.getD 0#32).toNat
  let v := lit / 2
  have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
    rw [hsh.trl_len]; have := hinv.assign.trl_end_le; unfold kMaxV at hnv; omega
  have hlit_lt : lit < 2 * ks.nv.toNat :=
    hinv.assign.trl_lt lit (mem_kittenTrailLits_of_lt hi1_lt htrl_len)
  have hrsn_len : v < ks.rsn.length := by
    rw [hsh.rsn_len]; unfold kMaxV at hnv; change lit / 2 < 128; omega
  have hrsn_eq2 : ks.rsn[v]?.getD 0#32 = rsn := by
    rw [hrsn_eq, List.getElem?_eq_getElem hrsn_len]; rfl
  rcases hro with hdec | ⟨hr_lt, _, hall⟩
  · exfalso; rw [hrsn_eq2] at hdec; exact hrsn_ne hdec
  · rw [hrsn_eq2] at hr_lt hall
    have hcm_len : rsn.toNat < cms.length := by
      rw [hloop.2.2.1]; unfold kMaxCl at hnc; omega
    have hcms' : ∀ c < ks.nc.toNat,
        (cms'[c]?.getD 0#32 &&& 0xFFFF#32) = (ks.clMeta[c]?.getD 0#32 &&& 0xFFFF#32) ∧
        (cms'[c]?.getD 0#32 &&& kmLrn) = (ks.clMeta[c]?.getD 0#32 &&& kmLrn) := by
      intro c hc
      by_cases hcr : c = rsn.toNat
      · subst hcr
        rw [show cms'[rsn.toNat]?.getD 0#32 = (cms[rsn.toNat]?.getD 0#32 ||| kmCore) by
          simp [cms', List.getElem?_set_self hcm_len]]
        rw [bv32_and_0xffff_or_core, bv32_and_lrn_or_core]
        exact hloop.2.2.2.1 rsn.toNat hc
      · simpa [cms', List.getElem?_set_ne (Ne.symm hcr)] using hloop.2.2.2.1 c hc
    refine ⟨by rw [hi_sub]; omega, hflj_len, by simp [cms', hloop.2.2.1], hcms', ?_⟩
    intro α hα
    rw [CNF.sat_append] at hα
    have hα_old : (cnfOfClauses (((List.range ks.nc.toNat).filter fun ci =>
        (cms[ci]?.getD 0#32 &&& kmCore) != 0#32).map (kittenClauseLits ks)) ++
        unitsCnf (kittenAssumpLits ks)).Sat α := by
      rw [CNF.sat_append]; refine ⟨?_, hα.2⟩
      rw [cnf_sat_cnfOfClauses_iff] at hα ⊢
      intro c hc
      rw [List.mem_map] at hc; obtain ⟨ci, hci, rfl⟩ := hc
      rw [List.mem_filter, List.mem_range] at hci
      apply hα.1; rw [List.mem_map]
      refine ⟨ci, List.mem_filter.mpr ⟨List.mem_range.mpr hci.1, ?_⟩, rfl⟩
      by_cases hcr : ci = rsn.toNat
      · subst hcr
        simp only [cms', List.getElem?_set_self hcm_len, Option.getD_some,
          bv32_and_core_or_core, bne_iff_ne, ne_eq, not_false_eq_true]
      · simpa [cms', List.getElem?_set_ne (Ne.symm hcr)] using hci.2
    obtain ⟨k, hk_lt, hk_fl, hk_sat⟩ := hloop.2.2.2.2 α hα_old
    by_cases hkl : k < i.toNat - 1
    · have hkv : (ks.trl[k]?.getD 0#32).toNat / 2 < ks.nv.toNat := by
        have hlt_k : k < ks.trl_end.toNat := by omega
        have := hinv.assign.trl_lt _ (mem_kittenTrailLits_of_lt hlt_k htrl_len); omega
      have hne_v : (ks.trl[k]?.getD 0#32).toNat / 2 ≠ v :=
        trl_nodup_var_ne_m5 hsh hnv hinv.assign (by omega) hi1_lt (by omega)
      refine ⟨k, by rw [hi_sub]; exact hkl, hkeep _ hkv ?_, hk_sat⟩
      rwa [hclr _ hkv hne_v]
    · have hkeq : k = i.toNat - 1 := by omega
      subst hkeq
      have hr_core : (cms'[rsn.toNat]?.getD 0#32 &&& kmCore) ≠ 0#32 := by
        rw [show cms'[rsn.toNat]?.getD 0#32 = (cms[rsn.toNat]?.getD 0#32 ||| kmCore) by
          simp [cms', List.getElem?_set_self hcm_len]]
        exact bv32_and_core_or_core _
      have hr_mem : kittenClauseLits ks rsn.toNat ∈ ((List.range ks.nc.toNat).filter fun ci =>
          (cms'[ci]?.getD 0#32 &&& kmCore) != 0#32).map (kittenClauseLits ks) :=
        List.mem_map.mpr ⟨rsn.toNat, List.mem_filter.mpr ⟨List.mem_range.mpr hr_lt,
          bne_iff_ne.mpr hr_core⟩, rfl⟩
      have hsat_r := (cnf_sat_cnfOfClauses_iff α _).mp hα.1 _ hr_mem
      obtain ⟨x, hx_mem, hxsat⟩ := (clause_sat_cnfClause_iff α _).mp hsat_r
      have hnot_lit : ¬ (cnfClause [lit]).Sat α := (sat_cnfClause_litNeg_iff α lit).mp hk_sat
      have hxne : x ≠ lit := fun h => hnot_lit (h ▸ (sat_cnfClause_singleton α x).mpr hxsat)
      obtain ⟨q, hq_lt, hq_eq⟩ := hall x hx_mem hxne
      have hx_mem_u := hx_mem
      unfold kittenClauseLits at hx_mem_u; rw [List.mem_map] at hx_mem_u
      obtain ⟨bx, hbx, rfl⟩ := hx_mem_u
      obtain ⟨r, hr, rfl⟩ := List.getElem_of_mem hbx
      have hr_sz : r < kittenClauseSize ks rsn.toNat := by simp [List.length_take] at hr; omega
      have har_lt_len : kittenClauseOff ks rsn.toNat + r < ks.arena.length := by
        have hwf_r := hinv.clauses.cl_wf rsn.toNat hr_lt
        have := hwf_r.2.2.1; unfold kittenClauseSpan at this
        rw [hsh.arena_len]; have := hinv.clauses.alen_le; omega
      have hbx_eq : ((ks.arena.drop (kittenClauseOff ks rsn.toNat)).take
          (kittenClauseSize ks rsn.toNat))[r] =
          ks.arena[kittenClauseOff ks rsn.toNat + r]?.getD 0#32 := by
        simp [List.getElem?_eq_getElem har_lt_len]
      have hne_qv : (ks.trl[q]?.getD 0#32).toNat / 2 ≠ v :=
        trl_nodup_var_ne_m5 hsh hnv hinv.assign (by omega) hi1_lt (by omega)
      have hx_div : (ks.arena[kittenClauseOff ks rsn.toNat + r]?.getD 0#32).toNat / 2 =
          (ks.trl[q]?.getD 0#32).toNat / 2 := by
        rw [← hbx_eq, hq_eq]
        rcases nat_xor1_cases
          (((ks.arena.drop (kittenClauseOff ks rsn.toNat)).take
            (kittenClauseSize ks rsn.toNat))[r]).toNat with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> omega
      have hmark_q := hmark r hr_sz (by rw [hx_div]; exact hne_qv)
      rw [hx_div] at hmark_q
      refine ⟨q, by rw [hi_sub]; exact hq_lt, hmark_q, ?_⟩
      rw [hq_eq, litNeg_eq_xor1, litNeg_litNeg]; simpa [← hbx_eq] using
        (sat_cnfClause_singleton α _).mpr hxsat

private theorem failingStepM5_skip {acap : Nat} {ks : KittenState}
    (_hsh : ks.ShapesOk acap) (hinv : ks.Inv acap) {i : BitVec 32}
    {fls cms : List (BitVec 32)}
    (hloop : FailingLoopInvM5 ks i fls cms) (hpos : 0 < i.toNat)
    (hzero : (fls[(ks.trl[i.toNat - 1]?.getD 0#32).toNat / 2]?.getD 0#32 &&& 2#32) = 0#32) :
    FailingLoopInvM5 ks (i - 1#32) fls cms := by
  have hnv := hinv.clauses.nv_le
  have hi_sub : (i - 1#32).toNat = i.toNat - 1 := by
    have := hloop.1; have := hinv.assign.trl_end_le; unfold kMaxV at hnv; bv_omega
  refine ⟨by rw [hi_sub]; have := hloop.1; omega, hloop.2.1, hloop.2.2.1, hloop.2.2.2.1, ?_⟩
  intro α hα
  obtain ⟨k, hk_lt, hk_fl, hk_sat⟩ := hloop.2.2.2.2 α hα
  refine ⟨k, ?_, hk_fl, hk_sat⟩
  rw [hi_sub]
  by_cases hkl : k < i.toNat - 1
  · exact hkl
  · exfalso; have hkeq : k = i.toNat - 1 := by omega
    subst hkeq; exact absurd hzero hk_fl

private theorem failingStepM5_dec {acap : Nat} {ks : KittenState}
    (hsh : ks.ShapesOk acap) (hinv : ks.Inv acap) (hdec : KittenAllDecisionsInAssumps ks)
    {i : BitVec 32} {fls fls_clr cms : List (BitVec 32)}
    (hloop : FailingLoopInvM5 ks i fls cms) (hpos : 0 < i.toNat)
    (hrsn : ks.rsn[(ks.trl[i.toNat - 1]?.getD 0#32).toNat / 2]?.getD 0#32 = 0xFFFFFFFF#32)
    (hclr_len : fls_clr.length = 128)
    (hclr : ∀ w < ks.nv.toNat, w ≠ (ks.trl[i.toNat - 1]?.getD 0#32).toNat / 2 →
      fls_clr[w]? = fls[w]?) :
    FailingLoopInvM5 ks (i - 1#32) fls_clr cms := by
  have hnv := hinv.clauses.nv_le
  have hi_le := hloop.1
  have hi1_lt : i.toNat - 1 < ks.trl_end.toNat := by omega
  have hi_sub : (i - 1#32).toNat = i.toNat - 1 := by
    have := hinv.assign.trl_end_le; unfold kMaxV at hnv; bv_omega
  have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
    rw [hsh.trl_len]; have := hinv.assign.trl_end_le; unfold kMaxV at hnv; omega
  refine ⟨by rw [hi_sub]; omega, hclr_len, hloop.2.2.1, hloop.2.2.2.1, ?_⟩
  intro α hα
  obtain ⟨k, hk_lt, hk_fl, hk_sat⟩ := hloop.2.2.2.2 α hα
  have hkne : k ≠ i.toNat - 1 := by
    intro hkeq
    have hk1 : k < ks.trl_end.toNat := by rw [hkeq]; exact hi1_lt
    have hrsn_k : ks.rsn[(ks.trl[k]?.getD 0#32).toNat / 2]?.getD 0#32 = 0xFFFFFFFF#32 := by
      rw [hkeq]; exact hrsn
    have hmem_dec : (ks.trl[k]?.getD 0#32).toNat ∈ kittenTrailDecisions ks :=
      (mem_kittenTrailDecisions_iff htrl_len).mpr ⟨k, hk1, rfl, hrsn_k⟩
    have hmem_ass := hdec _ hmem_dec
    have hsat_a := (sat_unitsCnf_iff α (kittenAssumpLits ks)).mp (CNF.sat_append.mp hα).2 _ hmem_ass
    exact ((sat_cnfClause_litNeg_iff α _).mp hk_sat) hsat_a
  have hne_v : (ks.trl[k]?.getD 0#32).toNat / 2 ≠ (ks.trl[i.toNat - 1]?.getD 0#32).toNat / 2 :=
    trl_nodup_var_ne_m5 hsh hnv hinv.assign (by omega) hi1_lt hkne
  have hkv : (ks.trl[k]?.getD 0#32).toNat / 2 < ks.nv.toNat := by
    have hlt_k : k < ks.trl_end.toNat := by omega
    have := hinv.assign.trl_lt _ (mem_kittenTrailLits_of_lt hlt_k htrl_len); omega
  refine ⟨k, by rw [hi_sub]; omega, ?_, hk_sat⟩
  rwa [hclr _ hkv hne_v]

private theorem failingFinishM5_preserves {acap : Nat} {ks : KittenState}
    (hsh : ks.ShapesOk acap) (hinv : ks.Inv acap) (hsync : KittenTrailSynced ks)
    {fls_fin cms_fin : List (BitVec 32)}
    (hloop : FailingLoopInvM5 ks 0#32 fls_fin cms_fin)
    (hclean : ∀ v < ks.nv.toNat, (fls_fin[v]?.getD 0#32 &&& 2#32) = 0#32) :
    let ks' : KittenState := { ks with failing := 1#32, flags := fls_fin, clMeta := cms_fin }
    ks'.Inv acap ∧ KittenTrailSynced ks' ∧ ks'.failing = 1#32 ∧
    KittenBuildFailingPreserved ks ks' := by
  intro ks'
  have hsh' : ks'.ShapesOk acap :=
    ⟨hsh.hdrTail_len, hsh.lvlArr_len, hsh.rsn_len, hsh.qprev_len, hsh.qnext_len,
      hsh.qstampArr_len, hsh.trl_len, hloop.2.1, hsh.vals_len, hsh.assump_len, hsh.ana_len,
      hsh.kl_len, hsh.units_len, hsh.res_len, hsh.whead_len, hsh.wnext_len, hsh.wblit_len,
      hsh.clOff_len, hloop.2.2.1, hsh.clAux_len, hsh.arena_len⟩
  have hcm_eq : ∀ c < ks.nc.toNat,
      (kittenClauseMeta ks' c &&& 0xFFFF#32) = (kittenClauseMeta ks c &&& 0xFFFF#32) ∧
      (kittenClauseMeta ks' c &&& kmLrn) = (kittenClauseMeta ks c &&& kmLrn) :=
    fun c hc => hloop.2.2.2.1 c hc
  have hsz_eq : ∀ c < ks.nc.toNat, kittenClauseSize ks' c = kittenClauseSize ks c := fun c hc => by
    unfold kittenClauseSize; rw [(hcm_eq c hc).1]
  have his_eq : ∀ c < ks.nc.toNat,
      kittenClauseIsLrn ks' c = kittenClauseIsLrn ks c := fun c hc => by
    unfold kittenClauseIsLrn; rw [(hcm_eq c hc).2]
  have hsp_eq : ∀ c < ks.nc.toNat, kittenClauseSpan ks' c = kittenClauseSpan ks c := fun c hc => by
    unfold kittenClauseSpan; rw [hsz_eq c hc, his_eq c hc]; rfl
  have hlits_eq : ∀ c < ks.nc.toNat,
      kittenClauseLits ks' c = kittenClauseLits ks c := fun c hc => by
    unfold kittenClauseLits; rw [hsz_eq c hc]; rfl
  have hants_eq : ∀ c < ks.nc.toNat,
      kittenClauseAnts ks' c = kittenClauseAnts ks c := fun c hc => by
    unfold kittenClauseAnts; rw [his_eq c hc, hsz_eq c hc]; rfl
  have horig_eq : kittenOrigClauses ks' = kittenOrigClauses ks :=
    kittenOrigClauses_eq_of rfl fun c hc =>
      hlits_eq c (Nat.lt_of_lt_of_le hc hinv.clauses.orig_nc_le)
  have hcl' : KittenClausesOk acap ks' := by
    have h0 := hinv.clauses
    refine ⟨h0.acap_ge, h0.acap_lt, h0.acap_eq, h0.nv_le, h0.nc_le, h0.orig_nc_le, h0.orig_nc_max,
      h0.alen_le, h0.nassump_le, h0.nunits_le, h0.nres_le, h0.nkl_le, h0.nana_le,
      ?_, ?_, ?_, ?_, ?_, h0.assump_ok, hclean⟩
    · intro c hc
      have hw := h0.cl_wf c hc
      rw [his_eq c hc, hsz_eq c hc, hsp_eq c hc, hlits_eq c hc, horig_eq, hants_eq c hc]
      refine ⟨hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1, fun ha hge => ?_⟩
      have ⟨ha1, ha2⟩ := hw.2.2.2.2.2 ha hge
      refine ⟨ha1, ?_⟩
      have hm : (kittenClauseAnts ks c).map (kittenClauseLits ks') =
          (kittenClauseAnts ks c).map (kittenClauseLits ks) :=
        List.map_congr_left fun a haa => hlits_eq a (Nat.lt_trans (ha1 a haa) hc)
      rwa [hm]
    · intro c1 c2 h12 hc2
      have hm := h0.cl_mono c1 c2 h12 hc2
      rwa [show kittenClauseOff ks' c1 = kittenClauseOff ks c1 from rfl,
        show kittenClauseOff ks' c2 = kittenClauseOff ks c2 from rfl,
        hsp_eq c1 (Nat.lt_trans h12 hc2)]
    · intro ui hui
      have hu := h0.units_ok ui hui
      refine ⟨hu.1, by rw [hsz_eq _ hu.1]; exact hu.2⟩
    · intro hi
      have hinc := h0.incons_ok hi
      refine ⟨hinc.1, by rw [horig_eq]; exact hinc.2.1, fun l hl => ?_⟩
      rw [hlits_eq _ hinc.1] at hl
      have hr := hinc.2.2 l hl
      refine ⟨hr.1, hr.2.1, fun ha => ?_⟩
      have hrr := hr.2.2 ha
      exact ⟨hrr.1, by rw [hlits_eq _ hrr.1]; exact hrr.2⟩
    · intro _ _
      rw [CNF.unsat_iff_not_sat]
      intro α hα
      have hsat : (cnfOfClauses (((List.range ks.nc.toNat).filter fun ci =>
          (cms_fin[ci]?.getD 0#32 &&& kmCore) != 0#32).map (kittenClauseLits ks)) ++
          unitsCnf (kittenAssumpLits ks)).Sat α := by
        rw [CNF.sat_append] at hα ⊢
        refine ⟨?_, hα.2⟩
        rw [cnf_sat_cnfOfClauses_iff] at hα ⊢
        intro cl hcl
        rw [List.mem_map] at hcl; obtain ⟨ci, hci, rfl⟩ := hcl
        rw [List.mem_filter, List.mem_range] at hci
        rw [← hlits_eq ci hci.1]
        exact hα.1 _ (List.mem_map.mpr ⟨ci, List.mem_filter.mpr ⟨List.mem_range.mpr hci.1,
          hci.2⟩, rfl⟩)
      obtain ⟨k, hk, _⟩ := hloop.2.2.2.2 α hsat
      rw [show (0#32 : BitVec 32).toNat = 0 from rfl] at hk
      exact absurd hk (Nat.not_lt_zero _)
  have hw' : KittenWatchesOk ks' := by
    obtain ⟨ch, hc1, hc2, hc3, hc4⟩ := hinv.watches
    refine ⟨ch, hc1, hc2, hc3, fun l hl w hw => ?_⟩
    have hb := hc4 l hl w hw
    exact ⟨hb.1, by rw [hsz_eq _ (Nat.div_lt_of_lt_mul hb.1)]; exact hb.2.1, hb.2.2.1, hb.2.2.2⟩
  have hba' : KittenBaseAssignOk ks' := by
    have h0 := hinv.assign
    refine ⟨h0.trl_end_le, h0.prop_le, h0.unass_eq, h0.vals_dom, h0.vals_neg_iff,
      h0.vals_nz_iff_trl, h0.trl_nodup, h0.trl_lt, h0.trl_lvl_le, h0.unass_lvl_zero,
      h0.trl_lvl_mono, h0.dec_earliest, fun i hi hlv => ?_⟩
    have hl0 := h0.lvl0_ok i hi hlv
    refine ⟨hl0.1, hl0.2.1, hl0.2.2.1, by rw [horig_eq]; exact hl0.2.2.2.1, fun ha => ?_⟩
    have hrr := hl0.2.2.2.2 ha
    exact ⟨hrr.1, by rw [hlits_eq _ hrr.1]; exact hrr.2⟩
  have hrsn' : Full.ReasonOk ks' := by
    intro i hi
    rcases hinv.reasons i hi with hd | ⟨hr_lt, hmem, hall⟩
    · exact Or.inl hd
    · right; rw [hlits_eq _ hr_lt]; exact ⟨hr_lt, hmem, hall⟩
  exact ⟨⟨hsh', hcl', hw', hba', hrsn'⟩, hsync, rfl,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, horig_eq,
      fun _ _ => rfl⟩⟩

/-! ## 3. `full_kitten_build_failing_m5_wp` (`Full.fullKittenBuildFailingSpec`) -/

/-- Parametric `Func.wp` proof for `full_kitten_build_failing_m5` (clears `KM_CORE` first). -/
theorem full_kitten_build_failing_m5_wp (Γ : Env) :
    ∀ args m Q X, fullKittenBuildFailingSpec args m Q X →
      Func.wp Γ full_kitten_build_failing_m5_body args m Q X := by
  rintro ⟨kPtr, alit, ⟨⟩⟩ m Q X ⟨acap, ks, R, hinv, hsync, halit, halit_mem, hval2, hdec, hm, hQ⟩
  have hsh := hinv.shapes
  have hcl := hinv.clauses
  have hnv := hcl.nv_le
  have hnc := hcl.nc_le
  have hnv_128 : ks.nv.toNat ≤ 128 := by unfold kMaxV at hnv; exact hnv
  have hnv_28 : ks.nv.toNat < 2 ^ 28 := by omega
  obtain ⟨halit_div, halit_lt⟩ := bv32_lit_div2_bv halit
  have halit_128 : (alit >>> (1 : Nat)).toNat < 128 := by omega
  have halit_28 : (alit >>> (1 : Nat)).toNat < 2 ^ 28 := by omega
  have halit_fl_len : (alit >>> (1 : Nat)).toNat < ks.flags.length := by
    rw [hsh.flags_len]; exact halit_128
  have hmA := kittenMem_to_amem hsh hm; clear hm
  c0_hsteps_nogrp
  -- Loop 0: clear `KM_CORE` across `0 .. nc`
  refine wp_while_state (proj := fun st : BitVec 32 × List (BitVec 32) => (st.1, ()))
    (fun st => ks.nc.toNat - st.1.toNat)
    (fun st m0 =>
      st.1.toNat ≤ ks.nc.toNat ∧ st.2.length = 896 ∧
      (∀ c < ks.nc.toNat,
        (st.2[c]?.getD 0#32 &&& 0xFFFF#32) = (ks.clMeta[c]?.getD 0#32 &&& 0xFFFF#32) ∧
        (st.2[c]?.getD 0#32 &&& kmLrn) = (ks.clMeta[c]?.getD 0#32 &&& kmLrn)) ∧
      (KittenMemA kPtr acap { ks with clMeta := st.2 } ⋆ R) m0)
    ?_ ?_
  · intro L0 hL0
    exact hL0 (0#32, ks.clMeta) m ⟨Nat.zero_le _, hsh.clMeta_len, fun _ _ => ⟨rfl, rfl⟩, hmA⟩
  · intro L0 ⟨ci, cms0⟩ m0 ⟨hci_le, hcms0_len, hbits0, hm0⟩ ih0
    dsimp only at hci_le hcms0_len hbits0 hm0 ⊢
    obtain ⟨ksC0, hksC0⟩ : ∃ x : KittenState, x = { ks with clMeta := cms0 } := ⟨_, rfl⟩
    rw [← hksC0] at hm0
    c0_hsplit
    · have hci_lt : ci.toNat < ks.nc.toNat := hc
      have hci_896 : ci.toNat < 896 := by unfold kMaxCl at hnc; omega
      have hci_28 : ci.toNat < 2 ^ 28 := by omega
      have hci1 : (ci + 1#32).toNat = ci.toNat + 1 := by bv_omega
      c0_hsteps!
      refine ih0 (ci + 1#32, cms0.set ci.toNat (cms0[ci.toNat]?.getD 0#32 &&& ~~~kmCore)) _
        (by dsimp only; rw [hci1]; omega)
        ⟨by dsimp only; rw [hci1]; omega, by simp [hcms0_len], ?_, ?_⟩
      · intro c hc_lt
        by_cases hcc : c = ci.toNat
        · subst hcc
          rw [List.getElem?_set_self (by omega), Option.getD_some,
            bv32_and_0xffff_and_not_core, bv32_and_lrn_and_not_core]
          exact hbits0 ci.toNat hc_lt
        · rw [List.getElem?_set_ne (Ne.symm hcc)]; exact hbits0 c hc_lt
      · refine Eq.mp (congrArg (fun x => (KittenMemA kPtr acap x ⋆ R) _) ?_) hm
        rw [hksC0]; kstate_ext <;> (first | rfl | kp_field)
    · c0_hsteps_nogrp
      -- Loop 1: clear `flags & ~2` across `0 .. nv`
      refine wp_while_state (proj := fun st : BitVec 32 × List (BitVec 32) => (st.1, ()))
        (fun st => ks.nv.toNat - st.1.toNat)
        (fun st m' =>
          st.1.toNat ≤ ks.nv.toNat ∧ st.2.length = 128 ∧
          (∀ v < st.1.toNat, (st.2[v]?.getD 0#32 &&& 2#32) = 0#32) ∧
          (KittenMemA kPtr acap { ks with flags := st.2, clMeta := cms0 } ⋆ R) m')
        ?_ ?_
      · intro L1 hL1
        refine hL1 (0#32, ks.flags) m0 ⟨Nat.zero_le _, hsh.flags_len, fun _ h => by simp at h, ?_⟩
        rwa [← hksC0]
      · intro L1 ⟨i, fls⟩ m' ⟨hi_le, hfls_len, hclr, hm'⟩ ih
        dsimp only at hi_le hfls_len hclr hm' ⊢
        obtain ⟨ksF, hksF⟩ : ∃ x : KittenState,
            x = { ks with flags := fls, clMeta := cms0 } := ⟨_, rfl⟩
        rw [← hksF] at hm'
        c0_hsplit
        · have hi_lt : i.toNat < ks.nv.toNat := by rw [hksC0] at hc; exact hc
          have hi_128 : i.toNat < 128 := by omega
          have hi_28 : i.toNat < 2 ^ 28 := by omega
          have hi1_wrap : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
          c0_hsteps!
          refine ih (i + 1#32, fls.set i.toNat (fls[i.toNat]?.getD 0#32 &&& ~~~2#32)) _
            (by dsimp only; rw [hi1_wrap]; omega) ⟨by dsimp only; rw [hi1_wrap]; omega,
              by simp [List.length_set, hfls_len], ?_, ?_⟩
          · intro v hv
            rw [hi1_wrap] at hv
            by_cases hvi : v = i.toNat
            · subst hvi
              rw [List.getElem?_set_self (by omega), Option.getD_some]
              exact fl_andnot2_and2_zero _
            · rw [List.getElem?_set_ne (Ne.symm hvi)]; exact hclr v (by omega)
          · refine Eq.mp (congrArg (fun x => (KittenMemA kPtr acap x ⋆ R) _) ?_) hm
            rw [hksF]; kstate_ext <;> (first | rfl | kp_field)
        · let fls1 := fls.set (alit >>> (1 : Nat)).toNat
            (fls[(alit >>> (1 : Nat)).toNat]?.getD 0#32 ||| 2#32)
          c0_hsteps_nogrp
          have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
            rw [hsh.trl_len]; have := hinv.assign.trl_end_le; omega
          obtain ⟨k0, hk0_lt, hk0_eq⟩ :=
            kitten_falsified_to_trail hsh hnv hinv.assign hsync halit hval2
          have hk0_div : (ks.trl[k0]?.getD 0#32).toNat / 2 = (alit >>> (1 : Nat)).toNat := by
            rw [hk0_eq, halit_div, ← litNeg_eq_xor1]
            rcases nat_xor1_cases alit.toNat with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> omega
          have hfls1_len : fls1.length = 128 := by simp [fls1, hfls_len]
          have hinit_loop : FailingLoopInvM5 ks ks.trl_end fls1 cms0 := by
            refine ⟨Nat.le_refl _, hfls1_len, hcms0_len, hbits0, fun α hα => ?_⟩
            have hsat_a := (sat_unitsCnf_iff α (kittenAssumpLits ks)).mp
              (CNF.sat_append.mp hα).2 alit.toNat halit_mem
            refine ⟨k0, hk0_lt, ?_, ?_⟩
            · rw [hk0_div]
              simp only [fls1,
                List.getElem?_set_self (by omega : (alit >>> (1 : Nat)).toNat < fls.length),
                Option.getD_some]
              exact fl_or2_and2_nz _
            · rw [hk0_eq, litNeg_litNeg]; exact hsat_a
          refine wp_while_state
            (proj := fun st : BitVec 32 × List (BitVec 32) × List (BitVec 32) => (st.1, ()))
            (fun st => st.1.toNat)
            (fun st m'' => FailingLoopInvM5 ks st.1 st.2.1 st.2.2 ∧
              (KittenMemA kPtr acap { ks with flags := st.2.1, clMeta := st.2.2 } ⋆ R) m'')
            ?_ ?_
          · intro L2 hL2
            refine wp_jump_state
              (proj := fun st : BitVec 32 × List (BitVec 32) × List (BitVec 32) => (st.1, ()))
              (ks.trl_end, fls1, cms0) (by rw [hksF]; kp_field; rfl)
              (hL2 (ks.trl_end, fls1, cms0) m ⟨hinit_loop, ?_⟩)
            refine Eq.mp (congrArg (fun x => (KittenMemA kPtr acap x ⋆ R) _) ?_) hm
            rw [hksF]; kstate_ext <;> (first | rfl | kp_field |
              (dsimp only [fls1]; simp only [halit_div, BitVec.toNat_ushiftRight,
                Nat.shiftRight_eq_div_pow, BitVec.ofNat_eq_ofNat]; simp))
          · intro L2 ⟨i2, fls2, cms2⟩ m2 ⟨hloop2, hm2⟩ ih2
            dsimp only at hloop2 hm2 ⊢
            obtain ⟨ksC, hksC⟩ : ∃ x : KittenState,
                x = { ks with flags := fls2, clMeta := cms2 } := ⟨_, rfl⟩
            rw [← hksC] at hm2
            c0_hsplit
            · have hi2_pos : 0 < i2.toNat := hc
              have hi2_le := hloop2.1
              have hi2_sub : (i2 - 1#32).toNat = i2.toNat - 1 := by
                have := hinv.assign.trl_end_le; bv_omega
              have hi2_sub_128 : (i2 - 1#32).toNat < 128 := by
                have := hinv.assign.trl_end_le; omega
              have hi2_sub_28 : (i2 - 1#32).toNat < 2 ^ 28 := by omega
              let tlit := ks.trl[(i2 - 1#32).toNat]?.getD 0#32
              have htlit_lt : tlit.toNat < 2 * ks.nv.toNat :=
                hinv.assign.trl_lt tlit.toNat (mem_kittenTrailLits_of_lt (by rw [hi2_sub]; omega)
                  htrl_len)
              obtain ⟨hv_div, hv_lt⟩ := bv32_lit_div2_bv htlit_lt
              have hbv_u1 : ∀ x : BitVec 32,
                  (x >>> (1 : BitVec 32)).toNat = (x >>> (1 : Nat)).toNat := fun _ => rfl
              have hv_128 : (tlit >>> (1 : Nat)).toNat < 128 := by omega
              have hv_28 : (tlit >>> (1 : Nat)).toNat < 2 ^ 28 := by omega
              have htlit_128 :
                  (ksC.trl[(i2 - 1).toNat]?.getD 0#32 >>> 1).toNat < 128 := by
                rw [hksC]; exact hv_128
              have htlit_bv28 :
                  (ksC.trl[(i2 - 1).toNat]?.getD 0#32 >>> 1).toNat < 2 ^ 28 := by
                rw [hksC]; exact hv_28
              c0_hsplit
              try (refine LeanQbe.T.wp_unroll_group fun _ _ => ?_; c0_hsplit)
              · have hzero_flag : (fls2[(tlit >>> (1 : Nat)).toNat]?.getD 0#32 &&& 2#32) = 0#32 :=
                  by rw [hksC] at hc; exact hc
                have hloop_skip := failingStepM5_skip hsh hinv hloop2 hi2_pos (by
                  rw [← hi2_sub]
                  change (fls2[tlit.toNat / 2]?.getD 0#32 &&& 2#32) = 0#32
                  rw [← hv_div]; exact hzero_flag)
                c0_hsteps!
                exact ih2 (i2 - 1#32, fls2, cms2) _ (by dsimp only; omega)
                  ⟨hloop_skip, by rw [hksC] at hm2; exact hm2⟩
              · have hnz_flag : (fls2[(tlit >>> (1 : Nat)).toNat]?.getD 0#32 &&& 2#32) ≠ 0#32 :=
                  by rw [hksC] at hc; exact hc
                let fls2_clr := fls2.set (tlit >>> (1 : Nat)).toNat
                  (fls2[(tlit >>> (1 : Nat)).toNat]?.getD 0#32 &&& ~~~2#32)
                have hclr_len : fls2_clr.length = 128 := by simp [fls2_clr, hloop2.2.1]
                have hclr_eq : ∀ w < ks.nv.toNat,
                    w ≠ (ks.trl[i2.toNat - 1]?.getD 0#32).toNat / 2 → fls2_clr[w]? = fls2[w]? := by
                  intro w _ hw
                  have hne_w : (tlit >>> (1 : Nat)).toNat ≠ w := by
                    rw [hv_div]; dsimp only [tlit]; rw [hi2_sub]; exact hw.symm
                  exact List.getElem?_set_ne hne_w
                c0_hsplit
                try (refine LeanQbe.T.wp_unroll_group fun _ _ => ?_; c0_hsplit)
                · have hi2_sub' :
                      (2 ^ 32 - BitVec.toNat (1 : BitVec 32) + i2.toNat) % 2 ^ 32 =
                        (i2 - 1#32).toNat := by
                    have := hinv.assign.trl_end_le; have := hloop2.1; bv_omega
                  have hrsn_fff :
                      ks.rsn[(tlit >>> (1 : Nat)).toNat]?.getD 0#32 = 0xFFFFFFFF#32 := by
                    have hc0 : ks.rsn[(ks.trl[(2 ^ 32 - BitVec.toNat (1 : BitVec 32) +
                        i2.toNat) % 2 ^ 32]?.getD 0#32).toNat / 2]?.getD 0#32 =
                        0xFFFFFFFF#32 := by rw [hksC] at hc; exact hc
                    rw [hi2_sub'] at hc0; rwa [hv_div]
                  have hrsn_fff2 :
                      ks.rsn[(ks.trl[i2.toNat - 1]?.getD 0#32).toNat / 2]?.getD 0#32 =
                        0xFFFFFFFF#32 := by rwa [← hi2_sub, ← hv_div]
                  have hloop_dec := failingStepM5_dec hsh hinv hdec hloop2 hi2_pos hrsn_fff2
                    hclr_len hclr_eq
                  c0_hsteps!
                  refine ih2 (i2 - 1#32, fls2_clr, cms2) _ (by dsimp only; omega) ⟨hloop_dec, ?_⟩
                  refine Eq.mp (congrArg (fun x => (KittenMemA kPtr acap x ⋆ R) _) ?_) hm
                  rw [hksC]; kstate_ext <;> (first | rfl | kp_field |
                    (dsimp only [fls2_clr, tlit]; simp [BitVec.toNat_ushiftRight,
                      Nat.shiftRight_eq_div_pow, BitVec.ofNat_eq_ofNat]))
                · have hi2_sub' :
                      (2 ^ 32 - BitVec.toNat (1 : BitVec 32) + i2.toNat) % 2 ^ 32 =
                        (i2 - 1#32).toNat := by
                    have := hinv.assign.trl_end_le; have := hloop2.1; bv_omega
                  let rsn := ks.rsn[(tlit >>> (1 : Nat)).toNat]?.getD 0#32
                  have hrsn_ne : rsn ≠ 0xFFFFFFFF#32 := by
                    have hc0 : ks.rsn[(ks.trl[(2 ^ 32 - BitVec.toNat (1 : BitVec 32) +
                        i2.toNat) % 2 ^ 32]?.getD 0#32).toNat / 2]?.getD 0#32 ≠
                        0xFFFFFFFF#32 := by rw [hksC] at hc; exact hc
                    rw [hi2_sub'] at hc0; dsimp only [rsn]; rwa [hv_div]
                  have hrsn_fff_eq : rsn =
                      ks.rsn[(ks.trl[i2.toNat - 1]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 := by
                    dsimp only [rsn]; rw [← hi2_sub, ← hv_div]
                    rw [List.getElem?_eq_getElem (by rw [hsh.rsn_len]; exact hv_128)]; rfl
                  have hro := hinv.reasons (i2.toNat - 1) (by omega)
                  dsimp only at hro
                  have hrsn_lt : rsn.toNat < ks.nc.toNat := by
                    have hr_get : ks.rsn[(ks.trl[i2.toNat - 1]?.getD 0#32).toNat / 2]?.getD 0#32 =
                        rsn := by dsimp only [rsn]; rw [← hi2_sub, ← hv_div]
                    rw [hr_get] at hro
                    rcases hro with hfff | ⟨hlt, _⟩
                    · exact absurd hfff hrsn_ne
                    · exact hlt
                  have hrsn_896 : rsn.toNat < 896 := by unfold kMaxCl at hnc; omega
                  have hrsn_28 : rsn.toNat < 2 ^ 28 := by omega
                  let cms2' := cms2.set rsn.toNat (cms2[rsn.toNat]?.getD 0#32 ||| kmCore)
                  let soff := ks.clOff[rsn.toNat]?.getD 0#32
                  let ssz := cms2'[rsn.toNat]?.getD 0#32 &&& 0xFFFF#32
                  have hssz_eq : ssz.toNat = kittenClauseSize ks rsn.toNat := by
                    dsimp only [ssz, cms2']
                    rw [List.getElem?_set_self (by rw [hloop2.2.2.1]; omega), Option.getD_some,
                      bv32_and_0xffff_or_core, (hloop2.2.2.2.1 rsn.toNat hrsn_lt).1]
                    rfl
                  have hwf_r := hcl.cl_wf rsn.toNat hrsn_lt
                  have hsoff_ssz : kittenClauseOff ks rsn.toNat + kittenClauseSize ks rsn.toNat ≤
                      ks.alen.toNat := by
                    have := hwf_r.2.2.1; unfold kittenClauseSpan at this; omega
                  have hm_m :
                      (KittenMemA kPtr acap { ks with flags := fls2_clr, clMeta := cms2 } ⋆ R) m :=
                    by
                    refine Eq.mp (congrArg (fun x => (KittenMemA kPtr acap x ⋆ R) _) ?_) hm
                    rw [hksC]; kstate_ext <;> (first | rfl | kp_field |
                      (dsimp only [fls2_clr, tlit]; simp [BitVec.toNat_ushiftRight,
                        Nat.shiftRight_eq_div_pow, BitVec.ofNat_eq_ofNat]))
                  clear hm
                  obtain ⟨ksM, hksM⟩ : ∃ x : KittenState,
                      x = { ks with flags := fls2_clr, clMeta := cms2 } := ⟨_, rfl⟩
                  have hm : (KittenMemA kPtr acap ksM ⋆ R) m := by rw [hksM]; exact hm_m
                  have hput_flags_rsn : ∀ (idx : Nat) (v : BitVec 32),
                      (ksC.putArr .flags idx v).rsn = ks.rsn :=
                    fun _ _ => by rw [hksC]; rfl
                  have htrl_ksC : ksC.trl = ks.trl := by rw [hksC]
                  have hrsn_c_eq :
                      ks.rsn[(ks.trl[(i2 - 1).toNat]?.getD 0#32 >>> (1 : Nat)).toNat]?.getD 0#32 =
                        rsn := by dsimp only [rsn, tlit]; rfl
                  have hrsn_c_eq' :
                      ks.rsn[(ks.trl[(i2 - 1#32).toNat]?.getD 0#32 >>> (1 : Nat)).toNat]?.getD
                        0#32 = rsn := by dsimp only [rsn, tlit]
                  rw [hput_flags_rsn, htrl_ksC]
                  try rw [hrsn_c_eq]
                  try rw [hrsn_c_eq']
                  c0_hsteps_nogrp
                  have hsz_g :
                      ((ksM.putArr .clMeta rsn.toNat (ksM.clMeta[rsn.toNat]?.getD 0#32 |||
                          (65536 : BitVec 32))).clMeta[rsn.toNat]?.getD 0#32 &&&
                        (65535 : BitVec 32)) = ssz := by
                    rw [hksM]; dsimp only [KittenState.putArr, ssz, cms2']
                    simp only [List.getElem?_set_self (by rw [hloop2.2.2.1]; omega),
                      Option.getD_some]
                    rfl
                  have hoff_g :
                      (ksM.putArr .clMeta rsn.toNat (ksM.clMeta[rsn.toNat]?.getD 0#32 |||
                          (65536 : BitVec 32))).clOff[rsn.toNat]?.getD 0#32 = soff := by
                    rw [hksM]; rfl
                  try rw [hoff_g]
                  try rw [hsz_g]
                  refine wp_while_state (proj := fun st : BitVec 32 × _ => (st.1, ()))
                    (fun st => ssz.toNat - st.1.toNat)
                    (fun st m3 =>
                      st.1.toNat ≤ ssz.toNat ∧ st.2.length = 128 ∧
                      (∀ w < ks.nv.toNat,
                        (fls2_clr[w]?.getD 0#32 &&& 2#32) ≠ 0#32 →
                        (st.2[w]?.getD 0#32 &&& 2#32) ≠ 0#32) ∧
                      (∀ q < st.1.toNat,
                        let lv := (ks.arena[kittenClauseOff ks rsn.toNat + q]?.getD 0#32).toNat / 2
                        lv ≠ (ks.trl[i2.toNat - 1]?.getD 0#32).toNat / 2 →
                        (st.2[lv]?.getD 0#32 &&& 2#32) ≠ 0#32) ∧
                      (KittenMemA kPtr acap { ks with flags := st.2, clMeta := cms2' } ⋆ R) m3)
                    ?_ ?_
                  · intro L3 hL3
                    refine hL3 (0#32, fls2_clr) _ ⟨Nat.zero_le _, hclr_len, fun _ _ h => h,
                      fun _ h => by simp at h, ?_⟩
                    refine Eq.mp (congrArg (fun x => (KittenMemA kPtr acap x ⋆ R) _) ?_) hm
                    rw [hksM]; kstate_ext <;> (first | rfl | kp_field)
                  · intro L3 ⟨j, fls3⟩ m3 ⟨hj_le, hfl3_len, hkeep3, hmark3, hm3⟩ ih3
                    dsimp only at hj_le hfl3_len hkeep3 hmark3 hm3 ⊢
                    obtain ⟨ksJ, hksJ⟩ : ∃ x : KittenState,
                        x = { ks with flags := fls3, clMeta := cms2' } := ⟨_, rfl⟩
                    rw [← hksJ] at hm3
                    c0_hsplit
                    · have hj_lt : j.toNat < ssz.toNat := hc
                      have hj_sz : j.toNat < kittenClauseSize ks rsn.toNat := by omega
                      have har_lt_a : kittenClauseOff ks rsn.toNat + j.toNat < ks.arena.length := by
                        rw [hsh.arena_len]; have := hcl.alen_le; omega
                      have har_28 : soff.toNat + j.toNat < 2 ^ 28 := by
                        change kittenClauseOff ks rsn.toNat + j.toNat < 2 ^ 28
                        have := hcl.alen_le; have := hcl.acap_lt; unfold dimacsBound at *; omega
                      have har_cap : soff.toNat + j.toNat < acap := by
                        change kittenClauseOff ks rsn.toNat + j.toNat < acap
                        have := hcl.alen_le; omega
                      have hlv_mem :
                          (ks.arena[kittenClauseOff ks rsn.toNat + j.toNat]'har_lt_a).toNat ∈
                            kittenClauseLits ks rsn.toNat := by
                        unfold kittenClauseLits; rw [List.mem_map]
                        refine ⟨ks.arena[kittenClauseOff ks rsn.toNat + j.toNat]'har_lt_a, ?_, rfl⟩
                        rw [List.mem_iff_getElem]
                        exact ⟨j.toNat, by
                            simp [List.length_take, List.length_drop]
                            rw [hsh.arena_len]; have := hcl.alen_le; omega,
                          by simp [List.getElem_take, List.getElem_drop]⟩
                      have hlv_lit := hwf_r.2.2.2.1 _ hlv_mem
                      let ot := ks.arena[soff.toNat + j.toNat]?.getD 0#32
                      have hot_eq :
                          ot = ks.arena[kittenClauseOff ks rsn.toNat + j.toNat]'har_lt_a := by
                        dsimp only [ot]
                        rw [show soff.toNat = kittenClauseOff ks rsn.toNat from rfl,
                          List.getElem?_eq_getElem har_lt_a, Option.getD_some]
                      obtain ⟨hlv_div, hlv_nv⟩ :=
                        bv32_lit_div2_bv (l := ot) (by rw [hot_eq]; exact hlv_lit)
                      have hlv_128 : (ot >>> (1 : Nat)).toNat < 128 := by omega
                      have hlv_28 : (ot >>> (1 : Nat)).toNat < 2 ^ 28 := by omega
                      have hlvJ_128 :
                          (ksJ.arena[soff.toNat + j.toNat]?.getD 0#32 >>> (1 : Nat)).toNat <
                            128 := by rw [hksJ]; exact hlv_128
                      have hlvJ_28 :
                          (ksJ.arena[soff.toNat + j.toNat]?.getD 0#32 >>> (1 : Nat)).toNat <
                            2 ^ 28 := by rw [hksJ]; exact hlv_28
                      have hj1_wrap : (j + 1#32).toNat = j.toNat + 1 := by bv_omega
                      c0_hsplit
                      try (refine LeanQbe.T.wp_unroll_group fun _ _ => ?_; c0_hsplit)
                      · have hne_lv : (ot >>> (1 : Nat)) ≠ (tlit >>> (1 : Nat)) := by
                          have hc0 : (ot >>> (1 : BitVec 32)) ≠ (tlit >>> (1 : BitVec 32)) := by
                            rw [hksJ] at hc; exact hc
                          intro heq; apply hc0
                          exact BitVec.eq_of_toNat_eq (by
                            rw [hbv_u1, hbv_u1]; exact congrArg BitVec.toNat heq)
                        let fls3' := fls3.set (ot >>> (1 : Nat)).toNat
                          (fls3[(ot >>> (1 : Nat)).toNat]?.getD 0#32 ||| 2#32)
                        c0_hsteps!
                        refine ih3 (j + 1#32, fls3') _ (by dsimp only; rw [hj1_wrap]; omega)
                          ⟨by dsimp only; rw [hj1_wrap]; omega, by simp [fls3', hfl3_len], ?_, ?_,
                           ?_⟩
                        · intro w hw hflw
                          by_cases hwo : w = (ot >>> (1 : Nat)).toNat
                          · subst hwo
                            simp only [fls3',
                              List.getElem?_set_self (by rw [hfl3_len]; exact hlv_128),
                              Option.getD_some]
                            exact fl_or2_and2_nz _
                          · dsimp only [fls3']
                            rw [List.getElem?_set_ne (Ne.symm hwo)]
                            exact hkeep3 w hw hflw
                        · intro q hq lv hne_q
                          dsimp only [lv] at hne_q ⊢
                          rw [hj1_wrap] at hq
                          by_cases hqj : q = j.toNat
                          · subst hqj
                            change (fls3'[ot.toNat / 2]?.getD 0#32 &&& 2#32) ≠ 0#32
                            rw [← hlv_div]
                            simp only [fls3',
                              List.getElem?_set_self (by rw [hfl3_len]; exact hlv_128),
                              Option.getD_some]
                            exact fl_or2_and2_nz _
                          · have hmk := hmark3 q (by omega) hne_q
                            by_cases hqo : (ks.arena[kittenClauseOff ks rsn.toNat + q]?.getD
                                0#32).toNat / 2 = (ot >>> (1 : Nat)).toNat
                            · rw [hqo]
                              simp only [fls3',
                                List.getElem?_set_self (by rw [hfl3_len]; exact hlv_128),
                                Option.getD_some]
                              exact fl_or2_and2_nz _
                            · dsimp only [fls3']
                              rw [List.getElem?_set_ne (Ne.symm hqo)]
                              exact hmk
                        · refine Eq.mp (congrArg (fun x => (KittenMemA kPtr acap x ⋆ R) _) ?_) hm
                          rw [hksJ]; kstate_ext <;> (first | rfl | kp_field)
                      · have heq_lv : (ot >>> (1 : Nat)) = (tlit >>> (1 : Nat)) := by
                          have hc0 : (ot >>> (1 : BitVec 32)) = (tlit >>> (1 : BitVec 32)) := by
                            rw [hksJ] at hc; exact hc
                          exact BitVec.eq_of_toNat_eq (by
                            rw [← hbv_u1, ← hbv_u1]; exact congrArg BitVec.toNat hc0)
                        c0_hsteps!
                        refine ih3 (j + 1#32, fls3) _ (by dsimp only; rw [hj1_wrap]; omega)
                          ⟨by dsimp only; rw [hj1_wrap]; omega, hfl3_len, hkeep3, ?_,
                            by rw [← hksJ]; exact hm3⟩
                        intro q hq lv hne_q
                        dsimp only [lv] at hne_q ⊢
                        rw [hj1_wrap] at hq
                        by_cases hqj : q = j.toNat
                        · subst hqj
                          exfalso; apply hne_q
                          change (ot.toNat / 2) = _
                          rw [← hlv_div, heq_lv, hv_div]
                          dsimp only [tlit]; rw [hi2_sub]
                        · exact hmark3 q (by omega) hne_q
                    · have hj_eq : j.toNat = ssz.toNat := by
                        have hhc : ¬ j.toNat < ssz.toNat := hc; omega
                      have hmark_all : ∀ q < kittenClauseSize ks rsn.toNat,
                          (ks.arena[kittenClauseOff ks rsn.toNat + q]?.getD 0#32).toNat / 2 ≠
                            (ks.trl[i2.toNat - 1]?.getD 0#32).toNat / 2 →
                          (fls3[(ks.arena[kittenClauseOff ks rsn.toNat + q]?.getD 0#32).toNat /
                            2]?.getD 0#32 &&& 2#32) ≠ 0#32 :=
                        fun q hq => hmark3 q (by omega)
                      have hloop_fin := failingStepM5_finish hsh hinv hloop2 hi2_pos hrsn_ne
                        hrsn_fff_eq hclr_eq hkeep3 hmark_all hfl3_len
                      c0_hsteps!
                      exact ih2 (i2 - 1#32, fls3, cms2') _ (by dsimp only; omega)
                        ⟨hloop_fin, by rw [hksJ] at hm3; exact hm3⟩
            · have hi2_eq : i2 = 0#32 := by
                have : ¬ 0 < i2.toNat := hc; bv_omega
              subst hi2_eq
              c0_hsteps_nogrp
              refine wp_while_state (proj := fun st : BitVec 32 × List (BitVec 32) => (st.1, ()))
                (fun st => ks.nv.toNat - st.1.toNat)
                (fun st m4 =>
                  st.1.toNat ≤ ks.nv.toNat ∧ st.2.length = 128 ∧
                  (∀ v < st.1.toNat, (st.2[v]?.getD 0#32 &&& 2#32) = 0#32) ∧
                  (KittenMemA kPtr acap { ks with flags := st.2, clMeta := cms2 } ⋆ R) m4)
                ?_ ?_
              · intro L4 hL4
                refine hL4 (0#32, fls2) _ ⟨Nat.zero_le _, hloop2.2.1, fun _ h => by simp at h,
                  by rw [hksC] at hm2; exact hm2⟩
              · intro L4 ⟨i4, fls4⟩ m4 ⟨hi4_le, hfl4_len, hclr4, hm4⟩ ih4
                dsimp only at hi4_le hfl4_len hclr4 hm4 ⊢
                obtain ⟨ks4, hks4⟩ : ∃ x : KittenState,
                    x = { ks with flags := fls4, clMeta := cms2 } := ⟨_, rfl⟩
                rw [← hks4] at hm4
                c0_hsplit
                · have hi4_lt : i4.toNat < ks.nv.toNat := by rw [hksC0] at hc; exact hc
                  have hi4_128 : i4.toNat < 128 := by omega
                  have hi4_28 : i4.toNat < 2 ^ 28 := by omega
                  have hi4_wrap : (i4 + 1#32).toNat = i4.toNat + 1 := by bv_omega
                  c0_hsteps!
                  refine ih4 (i4 + 1#32, fls4.set i4.toNat
                      (fls4[i4.toNat]?.getD 0#32 &&& ~~~2#32)) _
                    (by dsimp only; rw [hi4_wrap]; omega) ⟨by dsimp only; rw [hi4_wrap]; omega,
                      by simp [hfl4_len], ?_, ?_⟩
                  · intro v hv
                    rw [hi4_wrap] at hv
                    by_cases hvi : v = i4.toNat
                    · subst hvi
                      rw [List.getElem?_set_self (by omega), Option.getD_some]
                      exact fl_andnot2_and2_zero _
                    · rw [List.getElem?_set_ne (Ne.symm hvi)]; exact hclr4 v (by omega)
                  · refine Eq.mp (congrArg (fun x => (KittenMemA kPtr acap x ⋆ R) _) ?_) hm
                    rw [hks4]; kstate_ext <;> (first | rfl | kp_field)
                · have hi4_eq : i4.toNat = ks.nv.toNat := by
                    have hhc : ¬ i4.toNat < ks.nv.toNat := by rw [hksC0] at hc; exact hc
                    omega
                  have hclean_fin : ∀ v < ks.nv.toNat, (fls4[v]?.getD 0#32 &&& 2#32) = 0#32 :=
                    fun v hv => hclr4 v (by omega)
                  have hloop_fin : FailingLoopInvM5 ks 0#32 fls4 cms2 :=
                    ⟨Nat.zero_le _, hfl4_len, hloop2.2.2.1, hloop2.2.2.2.1, fun α hα => by
                      obtain ⟨k, hk, _⟩ := hloop2.2.2.2.2 α hα
                      rw [show (0#32 : BitVec 32).toNat = 0 from rfl] at hk
                      exact absurd hk (Nat.not_lt_zero _)⟩
                  have hfin := failingFinishM5_preserves hsh hinv hsync hloop_fin hclean_fin
                  c0_hsteps!
                  obtain ⟨_, hm_fin⟩ := kittenMemA_to_mem hm
                  refine hQ _ _ hfin.1 hfin.2.1 hfin.2.2.1 hfin.2.2.2
                    (Eq.mp (congrArg (fun x => (KittenMem kPtr x ⋆ R) _) ?_) hm_fin)
                  rw [hks4]; kstate_ext <;> (first | rfl | kp_field)

/-! ## 4. `full_kitten_core_m5_wp` (`Full.fullKittenCoreSpec`) -/

private def coreMarkedClausesM5 (ks : KittenState) (bound : Nat) : List (List Nat) :=
  ((List.range bound).filter fun ci =>
    (kittenClauseMeta ks ci &&& kmCore) != 0#32).map (kittenClauseLits ks)

private structure CoreMetaRelM5 (ks0 st : KittenState) : Prop where
  eq_with : st = { ks0 with clMeta := st.clMeta }
  clMeta_len : st.clMeta.length = 896
  bits_eq : ∀ (i : Nat),
    (st.clMeta[i]?.getD 0#32 &&& 0xFFFF#32) = (ks0.clMeta[i]?.getD 0#32 &&& 0xFFFF#32) ∧
    (st.clMeta[i]?.getD 0#32 &&& kmLrn) = (ks0.clMeta[i]?.getD 0#32 &&& kmLrn)

private theorem CoreMetaRelM5.refl {acap : Nat} {ks0 : KittenState}
    (hsh : ks0.ShapesOk acap) : CoreMetaRelM5 ks0 ks0 :=
  ⟨by cases ks0; rfl, hsh.clMeta_len, fun _ => ⟨rfl, rfl⟩⟩

private theorem CoreMetaRelM5.shapes {acap : Nat} {ks0 st : KittenState}
    (hsh : ks0.ShapesOk acap) (h : CoreMetaRelM5 ks0 st) : st.ShapesOk acap := by
  rw [h.eq_with]
  exact ⟨hsh.hdrTail_len, hsh.lvlArr_len, hsh.rsn_len, hsh.qprev_len, hsh.qnext_len,
    hsh.qstampArr_len, hsh.trl_len, hsh.flags_len, hsh.vals_len, hsh.assump_len, hsh.ana_len,
    hsh.kl_len, hsh.units_len, hsh.res_len, hsh.whead_len, hsh.wnext_len, hsh.wblit_len,
    hsh.clOff_len, h.clMeta_len, hsh.clAux_len, hsh.arena_len⟩

private theorem CoreMetaRelM5.clearCore {ks0 st : KittenState} (h : CoreMetaRelM5 ks0 st)
    (i : Nat) (hi : i < 896) :
    CoreMetaRelM5 ks0 (st.putArr .clMeta i (st.clMeta[i]?.getD 0#32 &&& ~~~kmCore)) := by
  have hlt : i < st.clMeta.length := by rw [h.clMeta_len]; exact hi
  refine ⟨by rw [h.eq_with]; rfl, by simp [KittenState.putArr, h.clMeta_len], fun k => ?_⟩
  simp only [KittenState.putArr]
  by_cases hki : k = i
  · subst hki
    rw [List.getElem?_set_self hlt, Option.getD_some,
      bv32_and_0xffff_and_not_core, bv32_and_lrn_and_not_core]
    exact h.bits_eq k
  · rw [List.getElem?_set_ne (Ne.symm hki)]; exact h.bits_eq k

private theorem CoreMetaRelM5.setCore {ks0 st : KittenState} (h : CoreMetaRelM5 ks0 st)
    (i : Nat) (hi : i < 896) :
    CoreMetaRelM5 ks0 (st.putArr .clMeta i (st.clMeta[i]?.getD 0#32 ||| kmCore)) := by
  have hlt : i < st.clMeta.length := by rw [h.clMeta_len]; exact hi
  refine ⟨by rw [h.eq_with]; rfl, by simp [KittenState.putArr, h.clMeta_len], fun k => ?_⟩
  simp only [KittenState.putArr]
  by_cases hki : k = i
  · subst hki
    rw [List.getElem?_set_self hlt, Option.getD_some,
      bv32_and_0xffff_or_core, bv32_and_lrn_or_core]
    exact h.bits_eq k
  · rw [List.getElem?_set_ne (Ne.symm hki)]; exact h.bits_eq k

private theorem CoreMetaRelM5.clause_fields {ks0 st : KittenState} (h : CoreMetaRelM5 ks0 st)
    (cid : Nat) :
    kittenClauseOff st cid = kittenClauseOff ks0 cid ∧
    kittenClauseSize st cid = kittenClauseSize ks0 cid ∧
    kittenClauseIsLrn st cid = kittenClauseIsLrn ks0 cid ∧
    kittenClauseAux st cid = kittenClauseAux ks0 cid ∧
    kittenClauseSpan st cid = kittenClauseSpan ks0 cid ∧
    kittenClauseLits st cid = kittenClauseLits ks0 cid ∧
    kittenClauseAnts st cid = kittenClauseAnts ks0 cid := by
  have hco : st.clOff = ks0.clOff := by rw [h.eq_with]
  have hca : st.clAux = ks0.clAux := by rw [h.eq_with]
  have har : st.arena = ks0.arena := by rw [h.eq_with]
  have hsz : kittenClauseSize st cid = kittenClauseSize ks0 cid := by
    simp only [kittenClauseSize, kittenClauseMeta, (h.bits_eq cid).1]
  have hlr : kittenClauseIsLrn st cid = kittenClauseIsLrn ks0 cid := by
    simp only [kittenClauseIsLrn, kittenClauseMeta, (h.bits_eq cid).2]
  have hoff : kittenClauseOff st cid = kittenClauseOff ks0 cid := by simp [kittenClauseOff, hco]
  have haux : kittenClauseAux st cid = kittenClauseAux ks0 cid := by simp [kittenClauseAux, hca]
  exact ⟨hoff, hsz, hlr, haux,
    by simp only [kittenClauseSpan, hsz, hlr, haux],
    by simp only [kittenClauseLits, hoff, hsz, har],
    by simp only [kittenClauseAnts, hlr, hoff, hsz, haux, har]⟩

private theorem CoreMetaRelM5.orig_eq {ks0 st : KittenState} (h : CoreMetaRelM5 ks0 st) :
    kittenOrigClauses st = kittenOrigClauses ks0 :=
  kittenOrigClauses_eq_of (by rw [h.eq_with]) fun ci _ => (h.clause_fields ci).2.2.2.2.2.1

private theorem CoreMetaRelM5.assump_eq {ks0 st : KittenState} (h : CoreMetaRelM5 ks0 st) :
    kittenAssumpLits st = kittenAssumpLits ks0 := by unfold kittenAssumpLits; rw [h.eq_with]

private theorem CoreMetaRelM5.toInv {acap : Nat} {ks0 st : KittenState}
    (hinv : ks0.Inv acap) (h : CoreMetaRelM5 ks0 st)
    (hfail : st.failing ≠ 0xFFFFFFFF#32 →
      (cnfOfClauses (coreMarkedClausesM5 st st.nc.toNat) ++
        unitsCnf (kittenAssumpLits st)).Unsat) :
    st.Inv acap := by
  have hsh := h.shapes hinv.shapes
  have e_nv : st.nv = ks0.nv := by rw [h.eq_with]
  have e_nc : st.nc = ks0.nc := by rw [h.eq_with]
  have e_on : st.orig_nc = ks0.orig_nc := by rw [h.eq_with]
  have e_al : st.alen = ks0.alen := by rw [h.eq_with]
  have e_ac : st.acap = ks0.acap := by rw [h.eq_with]
  have e_na : st.nassump = ks0.nassump := by rw [h.eq_with]
  have e_nu : st.nunits = ks0.nunits := by rw [h.eq_with]
  have e_nr : st.nres = ks0.nres := by rw [h.eq_with]
  have e_nk : st.nkl = ks0.nkl := by rw [h.eq_with]
  have e_nn : st.nana = ks0.nana := by rw [h.eq_with]
  have e_in : st.incons = ks0.incons := by rw [h.eq_with]
  have e_an : st.ante = ks0.ante := by rw [h.eq_with]
  have e_lv : st.lvl = ks0.lvl := by rw [h.eq_with]
  have e_pr : st.prop = ks0.prop := by rw [h.eq_with]
  have e_te : st.trl_end = ks0.trl_end := by rw [h.eq_with]
  have e_un : st.unass = ks0.unass := by rw [h.eq_with]
  have e_va : st.vals = ks0.vals := by rw [h.eq_with]
  have e_la : st.lvlArr = ks0.lvlArr := by rw [h.eq_with]
  have e_rs : st.rsn = ks0.rsn := by rw [h.eq_with]
  have e_tr : st.trl = ks0.trl := by rw [h.eq_with]
  have e_fl : st.flags = ks0.flags := by rw [h.eq_with]
  have e_as : st.assump = ks0.assump := by rw [h.eq_with]
  have e_ui : st.units = ks0.units := by rw [h.eq_with]
  have e_wh : st.whead = ks0.whead := by rw [h.eq_with]
  have e_wn : st.wnext = ks0.wnext := by rw [h.eq_with]
  have e_wb : st.wblit = ks0.wblit := by rw [h.eq_with]
  have e_ar : st.arena = ks0.arena := by rw [h.eq_with]
  have hcl : KittenClausesOk acap st := by
    refine ⟨hinv.clauses.acap_ge, hinv.clauses.acap_lt, by rw [e_ac]; exact hinv.clauses.acap_eq,
      by rw [e_nv]; exact hinv.clauses.nv_le, by rw [e_nc]; exact hinv.clauses.nc_le,
      by rw [e_on, e_nc]; exact hinv.clauses.orig_nc_le,
      by rw [e_on]; exact hinv.clauses.orig_nc_max, by rw [e_al]; exact hinv.clauses.alen_le,
      by rw [e_na]; exact hinv.clauses.nassump_le, by rw [e_nu]; exact hinv.clauses.nunits_le,
      by rw [e_nr]; exact hinv.clauses.nres_le, by rw [e_nk]; exact hinv.clauses.nkl_le,
      by rw [e_nn]; exact hinv.clauses.nana_le, ?_, ?_, ?_, ?_, fun _ => hfail, ?_, ?_⟩
    · intro cid hcid
      have hw := hinv.clauses.cl_wf cid (e_nc ▸ hcid)
      have hf := h.clause_fields cid
      rw [hf.2.2.1, hf.2.1, hf.1, hf.2.2.2.2.1, hf.2.2.2.2.2.1, hf.2.2.2.2.2.2,
        List.map_congr_left (fun a _ => (h.clause_fields a).2.2.2.2.2.1),
        e_on, e_al, e_nv, e_an, h.orig_eq]
      exact hw
    · intro c1 c2 h12 hc2
      rw [(h.clause_fields c1).1, (h.clause_fields c1).2.2.2.2.1, (h.clause_fields c2).1]
      exact hinv.clauses.cl_mono c1 c2 h12 (e_nc ▸ hc2)
    · intro ui hui
      dsimp only; rw [e_ui, e_nc, (h.clause_fields _).2.1]
      exact hinv.clauses.units_ok ui (e_nu ▸ hui)
    · intro hi
      have hinc := hinv.clauses.incons_ok (e_in ▸ hi)
      refine ⟨by rw [e_in, e_nc]; exact hinc.1, by rw [h.orig_eq]; exact hinc.2.1, fun l hl => ?_⟩
      rw [e_in, (h.clause_fields _).2.2.2.2.2.1] at hl
      have hr := hinc.2.2 l hl
      dsimp only at hr ⊢; rw [e_va, e_la, e_rs, e_nc]
      refine ⟨hr.1, hr.2.1, fun ha => ?_⟩
      have hrr := hr.2.2 (e_an ▸ ha)
      rw [(h.clause_fields _).2.2.2.2.2.1]; exact hrr
    · intro i hi; rw [e_as, e_nv]; exact hinv.clauses.assump_ok i (e_na ▸ hi)
    · intro v hv; rw [e_fl]; exact hinv.clauses.flags_clean v (e_nv ▸ hv)
  have hw : KittenWatchesOk st := by
    obtain ⟨ch, h1, h2, h3, h4⟩ := hinv.watches
    refine ⟨ch, e_nv ▸ h1, h2, fun l hl => by rw [e_wn, e_wh]; exact h3 l (e_nv ▸ hl),
      fun l hl w hw => ?_⟩
    have hb := h4 l (e_nv ▸ hl) w hw
    rw [e_nc, e_nv, e_ar, e_wb, (h.clause_fields _).2.1, (h.clause_fields _).1]; exact hb
  have hba : KittenBaseAssignOk st :=
    ⟨by rw [e_te, e_nv]; exact hinv.assign.trl_end_le,
     by rw [e_pr, e_te]; exact hinv.assign.prop_le,
     by rw [e_un, e_te, e_nv]; exact hinv.assign.unass_eq,
     by rw [e_nv, e_va]; exact hinv.assign.vals_dom,
     by rw [e_nv, e_va]; exact hinv.assign.vals_neg_iff,
     by rw [e_nv, e_va, e_te, e_tr]; exact hinv.assign.vals_nz_iff_trl,
     by unfold kittenTrailLits; rw [e_te, e_tr]; exact hinv.assign.trl_nodup,
     by unfold kittenTrailLits; rw [e_nv, e_te, e_tr]; exact hinv.assign.trl_lt,
     by rw [e_nv, e_la, e_lv]; exact hinv.assign.trl_lvl_le,
     by rw [e_nv, e_va, e_la, e_rs]; exact hinv.assign.unass_lvl_zero,
     by rw [e_te, e_la, e_tr]; exact hinv.assign.trl_lvl_mono,
     by rw [e_te, e_la, e_tr, e_rs]; exact hinv.assign.dec_earliest,
     by intro i hi l hlv
        rw [e_te] at hi; dsimp only [l] at hlv ⊢; rw [e_tr, e_la] at hlv
        rw [e_tr, e_rs, e_va, h.orig_eq, e_nc]
        have h0 := hinv.assign.lvl0_ok i hi hlv
        refine ⟨h0.1, h0.2.1, h0.2.2.1, h0.2.2.2.1, fun ha => ?_⟩
        have hr := h0.2.2.2.2 (e_an ▸ ha)
        dsimp only at hr ⊢; rw [(h.clause_fields _).2.2.2.2.2.1]; exact hr⟩
  have hrsn : Full.ReasonOk st := by
    intro i hi; rw [e_te] at hi; dsimp only; rw [e_tr, e_rs, e_nc]
    have hr := hinv.reasons i hi; dsimp only at hr
    simpa only [(h.clause_fields _).2.2.2.2.2.1] using hr
  exact ⟨hsh, hcl, hw, hba, hrsn⟩

private theorem coreMarkedM5_unsat_mono {ks0 st1 st2 : KittenState}
    (h1 : CoreMetaRelM5 ks0 st1) (h2 : CoreMetaRelM5 ks0 st2)
    (hmono : ∀ c < ks0.nc.toNat,
      (kittenClauseMeta st1 c &&& kmCore) ≠ 0#32 → (kittenClauseMeta st2 c &&& kmCore) ≠ 0#32)
    (huns : (cnfOfClauses (coreMarkedClausesM5 st1 ks0.nc.toNat) ++
      unitsCnf (kittenAssumpLits ks0)).Unsat) :
    (cnfOfClauses (coreMarkedClausesM5 st2 ks0.nc.toNat) ++
      unitsCnf (kittenAssumpLits ks0)).Unsat := by
  rw [CNF.unsat_iff_not_sat] at huns ⊢
  intro α hα; apply huns α; rw [CNF.sat_append] at hα ⊢
  refine ⟨?_, hα.2⟩; rw [cnf_sat_cnfOfClauses_iff] at hα ⊢
  intro cl hcl; unfold coreMarkedClausesM5 at hcl; rw [List.mem_map] at hcl
  obtain ⟨ci, hci, rfl⟩ := hcl; rw [List.mem_filter, List.mem_range] at hci
  have hnz2 := hmono ci hci.1 (by simpa [bne_iff_ne] using hci.2)
  rw [(h1.clause_fields ci).2.2.2.2.2.1.trans (h2.clause_fields ci).2.2.2.2.2.1.symm]
  exact hα.1 _ (List.mem_map.mpr ⟨ci,
    List.mem_filter.mpr ⟨List.mem_range.mpr hci.1, by simpa [bne_iff_ne] using hnz2⟩, rfl⟩)

private theorem coreMarkedM5_setCore_unsat {ks0 st : KittenState}
    (h : CoreMetaRelM5 ks0 st) {idx : Nat} (hi : idx < 896)
    (huns : (cnfOfClauses (coreMarkedClausesM5 st ks0.nc.toNat) ++
      unitsCnf (kittenAssumpLits ks0)).Unsat) :
    let st' := st.putArr .clMeta idx (st.clMeta[idx]?.getD 0#32 ||| kmCore)
    (cnfOfClauses (coreMarkedClausesM5 st' ks0.nc.toNat) ++
      unitsCnf (kittenAssumpLits ks0)).Unsat := by
  intro st'
  refine coreMarkedM5_unsat_mono h (h.setCore idx hi) (fun c _ hc => ?_) huns
  by_cases hci : c = idx
  · subst hci
    have hlt : c < st.clMeta.length := by rw [h.clMeta_len]; exact hi
    change ((st.clMeta.set c (st.clMeta[c]?.getD 0#32 ||| kmCore))[c]?.getD 0#32 &&& kmCore) ≠ 0#32
    rw [List.getElem?_set_self hlt, Option.getD_some]; exact bv32_and_core_or_core _
  · change ((st.clMeta.set idx _)[c]?.getD 0#32 &&& kmCore) ≠ 0#32
    rw [List.getElem?_set_ne (Ne.symm hci)]; exact hc

private theorem coreM5_incons_seeded_unsat {acap : Nat} {ks0 st : KittenState}
    (hinv : ks0.Inv acap) (hrel : CoreMetaRelM5 ks0 st)
    (hante : ks0.ante ≠ 0#32) (hinc : ks0.incons ≠ 0xFFFFFFFF#32)
    (hmark_inc : (kittenClauseMeta st ks0.incons.toNat &&& kmCore) ≠ 0#32)
    (hmark_rsn : ∀ j < kittenClauseSize ks0 ks0.incons.toNat,
      let l := (ks0.arena[kittenClauseOff ks0 ks0.incons.toNat + j]?.getD 0#32).toNat
      let r0 := (ks0.rsn[l / 2]?.getD 0#32).toNat
      (kittenClauseMeta st r0 &&& kmCore) ≠ 0#32) :
    (cnfOfClauses (coreMarkedClausesM5 st ks0.nc.toNat) ++
      unitsCnf (kittenAssumpLits ks0)).Unsat := by
  refine cnfOfClauses_unsat_append_left _ ?_
  rw [CNF.unsat_iff_not_sat]; intro α hα
  have hio := hinv.clauses.incons_ok hinc
  have hinc_mem : kittenClauseLits st ks0.incons.toNat ∈ coreMarkedClausesM5 st ks0.nc.toNat :=
    List.mem_map.mpr ⟨ks0.incons.toNat,
      List.mem_filter.mpr ⟨List.mem_range.mpr hio.1, by simpa [bne_iff_ne] using hmark_inc⟩, rfl⟩
  have hsat_inc := (cnf_sat_cnfOfClauses_iff α _).mp hα _ hinc_mem
  rw [(hrel.clause_fields _).2.2.2.2.2.1, clause_sat_cnfClause_iff] at hsat_inc
  obtain ⟨l, hl_mem, hlsat⟩ := hsat_inc
  have hwf := hinv.clauses.cl_wf ks0.incons.toNat hio.1
  have hl_lt : l < 2 * ks0.nv.toNat := hwf.2.2.2.1 l hl_mem
  have hspan : kittenClauseOff ks0 ks0.incons.toNat + kittenClauseSize ks0 ks0.incons.toNat ≤
      ks0.arena.length := by
    rw [hinv.shapes.arena_len]
    have h1 := hwf.2.2.1; unfold kittenClauseSpan at h1
    have h2 := hinv.clauses.alen_le; omega
  have hlen_lits : (kittenClauseLits ks0 ks0.incons.toNat).length =
      kittenClauseSize ks0 ks0.incons.toNat := by
    simp only [kittenClauseLits, List.length_map, List.length_take, List.length_drop]; omega
  obtain ⟨j, hj_len, hj_eq⟩ := List.getElem_of_mem hl_mem
  have hj_lt : j < kittenClauseSize ks0 ks0.incons.toNat := hlen_lits ▸ hj_len
  have hl_eq_ar : (ks0.arena[kittenClauseOff ks0 ks0.incons.toNat + j]?.getD 0#32).toNat = l := by
    rw [← hj_eq]
    simp only [kittenClauseLits, List.getElem_map, List.getElem_take, List.getElem_drop]
    rw [List.getElem?_eq_getElem (by omega : kittenClauseOff ks0 ks0.incons.toNat + j <
      ks0.arena.length), Option.getD_some]
  have hmr := hmark_rsn j hj_lt; dsimp only at hmr; rw [hl_eq_ar] at hmr
  have hr_ok := (hio.2.2 l hl_mem).2.2 hante; dsimp only at hr_ok
  have hrs_len : l / 2 < ks0.rsn.length := by
    rw [hinv.shapes.rsn_len]; have := hinv.clauses.nv_le; unfold kMaxV at this; omega
  have hrs_eq : ks0.rsn[l / 2]?.getD 0#32 = ks0.rsn[l / 2]?.getD 0xFFFFFFFF#32 := by
    rw [List.getElem?_eq_getElem hrs_len, Option.getD_some, Option.getD_some]
  rw [hrs_eq] at hmr
  let r0 := (ks0.rsn[l / 2]?.getD 0xFFFFFFFF#32).toNat
  have hr_mem : kittenClauseLits st r0 ∈ coreMarkedClausesM5 st ks0.nc.toNat :=
    List.mem_map.mpr ⟨r0,
      List.mem_filter.mpr ⟨List.mem_range.mpr hr_ok.1, by simpa [bne_iff_ne] using hmr⟩, rfl⟩
  have hsat_r := (cnf_sat_cnfOfClauses_iff α _).mp hα _ hr_mem
  rw [(hrel.clause_fields r0).2.2.2.2.2.1, hr_ok.2, litNeg_eq_xor1] at hsat_r
  exact (sat_cnfClause_litNeg_iff α l).mp hsat_r ((sat_cnfClause_singleton α l).mpr hlsat)

private theorem coreM5_dag_entails {acap : Nat} {ks0 st : KittenState}
    (hinv : ks0.Inv acap) (hrel : CoreMetaRelM5 ks0 st) (hante : ks0.ante ≠ 0#32)
    (hdag : ∀ c < ks0.nc.toNat, (kittenClauseMeta st c &&& kmCore) ≠ 0#32 →
      ks0.orig_nc.toNat ≤ c →
      ∀ a ∈ kittenClauseAnts ks0 c, (kittenClauseMeta st a &&& kmCore) ≠ 0#32) :
    ∀ c < ks0.nc.toNat, (kittenClauseMeta st c &&& kmCore) ≠ 0#32 →
      (cnfOfClauses (kittenCoreClauses st)).EntailsClause (cnfClause (kittenClauseLits st c)) := by
  intro c
  induction c using Nat.strongRecOn with
  | ind c ih =>
    intro hc hcm
    by_cases horig : c < ks0.orig_nc.toNat
    · apply cnfOfClauses_entailsClause_of_mem
      unfold kittenCoreClauses; rw [List.mem_map]
      have e_on : st.orig_nc = ks0.orig_nc := by rw [hrel.eq_with]
      exact ⟨c, List.mem_filter.mpr ⟨List.mem_range.mpr (e_on ▸ horig),
        by simpa [bne_iff_ne] using hcm⟩, rfl⟩
    · have hge : ks0.orig_nc.toNat ≤ c := Nat.le_of_not_lt horig
      have hwf := (hinv.clauses.cl_wf c hc).2.2.2.2.2 hante hge
      rw [CNF.entails_clause_def]; intro α hα
      rw [(hrel.clause_fields c).2.2.2.2.2.1]
      apply CNF.entails_clause_def.mp hwf.2 α
      rw [cnf_sat_cnfOfClauses_iff]; intro cl hcl
      rw [List.mem_map] at hcl; obtain ⟨a, ha, rfl⟩ := hcl
      have ha_lt : a < c := hwf.1 a ha
      have hent := ih a ha_lt (Nat.lt_trans ha_lt hc) (hdag c hc hcm hge a ha)
      rw [(hrel.clause_fields a).2.2.2.2.2.1] at hent
      exact CNF.entails_clause_def.mp hent α hα

private theorem coreM5_dag_unsat {acap : Nat} {ks0 st : KittenState}
    (hinv : ks0.Inv acap) (hrel : CoreMetaRelM5 ks0 st) (hante : ks0.ante ≠ 0#32)
    (huns : (cnfOfClauses (coreMarkedClausesM5 st ks0.nc.toNat) ++
      unitsCnf (kittenAssumpLits ks0)).Unsat)
    (hdag : ∀ c < ks0.nc.toNat, (kittenClauseMeta st c &&& kmCore) ≠ 0#32 →
      ks0.orig_nc.toNat ≤ c →
      ∀ a ∈ kittenClauseAnts ks0 c, (kittenClauseMeta st a &&& kmCore) ≠ 0#32) :
    (cnfOfClauses (kittenCoreClauses st) ++ unitsCnf (kittenAssumpLits st)).Unsat := by
  rw [hrel.assump_eq, CNF.unsat_iff_not_sat]; intro α hα
  rw [CNF.sat_append] at hα; rw [CNF.unsat_iff_not_sat] at huns
  apply huns α; rw [CNF.sat_append]; refine ⟨?_, hα.2⟩
  rw [cnf_sat_cnfOfClauses_iff]; intro cl hcl
  unfold coreMarkedClausesM5 at hcl; rw [List.mem_map] at hcl
  obtain ⟨ci, hci, rfl⟩ := hcl; rw [List.mem_filter, List.mem_range] at hci
  exact CNF.entails_clause_def.mp
    (coreM5_dag_entails hinv hrel hante hdag ci hci.1 (by simpa [bne_iff_ne] using hci.2)) α hα.1

private theorem mem_kittenCoreClausesM5_orig (ks : KittenState) :
    ∀ cl ∈ kittenCoreClauses ks, cl ∈ kittenOrigClauses ks := by
  intro cl hcl; unfold kittenCoreClauses at hcl; unfold kittenOrigClauses
  rw [List.mem_map] at hcl ⊢; obtain ⟨ci, hci, rfl⟩ := hcl
  exact ⟨ci, (List.mem_filter.mp hci).1, rfl⟩

/-- Parametric `Func.wp` proof for `full_kitten_core_m5`. -/
theorem full_kitten_core_m5_wp (Γ : Env) :
    ∀ args m Q X, fullKittenCoreSpec args m Q X →
      Func.wp Γ full_kitten_core_m5_body args m Q X := by
  rintro ⟨hPtr, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hinv_s, hante, hor_if, hm, hQ⟩
  rcases hinv_s with ⟨hscr_ge, hscr_lt, hinv⟩
  let scr := s.scratch.scratch_buf
  change kMinScratchCap ≤ scr.length at hscr_ge
  change scr.length < dimacsBound at hscr_lt
  have hscr_len : scr.length = c.scratch_cap := hlen.scratch_ok.scratch_buf_len
  have hscr_8864 : 8864 ≤ scr.length := by unfold kMinScratchCap at hscr_ge; omega
  let acap := scr.length - 8864
  let ks0 := kittenStateOfScratch scr
  change ks0.Inv acap at hinv
  change ks0.ante ≠ 0#32 at hante
  change ks0.incons ≠ 0xFFFFFFFF#32 ∨ ks0.failing ≠ 0xFFFFFFFF#32 at hor_if
  have hsh0 := hinv.shapes; have hcl0 := hinv.clauses
  have hnv := hcl0.nv_le; have hnc := hcl0.nc_le
  have honc := hcl0.orig_nc_le; have hal := hcl0.alen_le
  have hacap_lt : acap < 2 ^ 28 := hcl0.acap_lt
  have hmF : (FullKittenFrame c s ⋆ KittenMem (c.pScratchBuf + 1024#64) ks0 ⋆ R) m := by
    have hfull := fullMem_eq_kittenFrame (c := c) (s := s) hscr_8864
    rw [hfull] at hm; exact sep_ac hm
  clear hm
  c0_hsteps_nogrp
  let kPtr := c.pScratchBuf + BitVec.ofNat 64 256 * 4
  have hmA : (KittenMemA kPtr acap ks0 ⋆ (FullKittenFrame c s ⋆ R)) m := by
    have hm1 : (KittenMem kPtr ks0 ⋆ (FullKittenFrame c s ⋆ R)) m := by
      dsimp only [kPtr]; rw [kPtr_base_eq]; exact sep_ac hmF
    exact kittenMem_to_amem hsh0 hm1
  clear hmF
  c0_hsteps_nogrp
  refine wp_join_state0 (α := KittenState)
    (fun st m1 => CoreMetaRelM5 ks0 st ∧
      (cnfOfClauses (coreMarkedClausesM5 st ks0.nc.toNat) ++
        unitsCnf (kittenAssumpLits ks0)).Unsat ∧
      (KittenMemA kPtr acap st ⋆ (FullKittenFrame c s ⋆ R)) m1) ?_ ?_
  · intro J1 st1 m1 ⟨hrel1, huns1, hm1⟩
    c0_hsteps_nogrp
    have hnc_eq1 : st1.nc = ks0.nc := by rw [hrel1.eq_with]
    refine wp_while_state1 (fun p : BitVec 32 × KittenState => p.1)
      (fun p => p.1.toNat)
      (fun p m2 => p.1.toNat ≤ ks0.nc.toNat ∧ CoreMetaRelM5 ks0 p.2 ∧
        (cnfOfClauses (coreMarkedClausesM5 p.2 ks0.nc.toNat) ++
          unitsCnf (kittenAssumpLits ks0)).Unsat ∧
        (∀ c, p.1.toNat ≤ c → c < ks0.nc.toNat →
          (kittenClauseMeta p.2 c &&& kmCore) ≠ 0#32 → ks0.orig_nc.toNat ≤ c →
          ∀ a ∈ kittenClauseAnts ks0 c, (kittenClauseMeta p.2 a &&& kmCore) ≠ 0#32) ∧
        (KittenMemA kPtr acap p.2 ⋆ (FullKittenFrame c s ⋆ R)) m2)
      ?_ ?_
    · intro J2 hJ2
      exact wp_jump_state (proj := fun p : BitVec 32 × KittenState => (p.1, ()))
        (ks0.nc, st1) rfl
        (hJ2 _ m1 ⟨Nat.le_refl _, hrel1, huns1, fun c h1 h2 => by dsimp only at h1; omega, hm1⟩)
    · rintro J2 ⟨cid, st2⟩ m2 ⟨hcid_le, hrel2, huns2, hdag2, hm2⟩ ih2
      dsimp only at hcid_le hrel2 huns2 hdag2 hm2
      c0_hsplit
      · have hcid_pos : 0 < cid.toNat := by bv_omega
        let cid' := cid - 1#32
        have hcid'_eq : cid'.toNat = cid.toNat - 1 := by dsimp only [cid']; bv_omega
        have hcid'_lt : cid'.toNat < ks0.nc.toNat := by omega
        have hcid'_896 : cid'.toNat < 896 := by unfold kMaxCl at hnc; omega
        have hcid'_wrap : cid'.toNat < 2 ^ 28 := by omega
        c0_hsteps_nogrp
        let mval := st2.clMeta[cid'.toNat]?.getD 0#32
        have hwf_c := hcl0.cl_wf cid'.toNat hcid'_lt
        refine wp_join_state0 (α := KittenState)
          (fun st3 m3 => CoreMetaRelM5 ks0 st3 ∧
            (cnfOfClauses (coreMarkedClausesM5 st3 ks0.nc.toNat) ++
              unitsCnf (kittenAssumpLits ks0)).Unsat ∧
            (∀ c, cid'.toNat ≤ c → c < ks0.nc.toNat →
              (kittenClauseMeta st3 c &&& kmCore) ≠ 0#32 → ks0.orig_nc.toNat ≤ c →
              ∀ a ∈ kittenClauseAnts ks0 c, (kittenClauseMeta st3 a &&& kmCore) ≠ 0#32) ∧
            (KittenMemA kPtr acap st3 ⋆ (FullKittenFrame c s ⋆ R)) m3) ?_ ?_
        · intro J3 st3 m3 ⟨hrel3, huns3, hdag3, hm3⟩
          c0_hsteps_nogrp
          exact ih2 (cid', st3) m3 (by dsimp only; omega)
            ⟨by dsimp only; omega, hrel3, huns3, hdag3, hm3⟩
        · intro J3 hJ3
          c0_hsplit
          · c0_hsplit
            · have hcore_c : (mval &&& kmCore) ≠ 0#32 := ‹_›
              have hlrn_c : (mval &&& kmLrn) ≠ 0#32 := ‹_›
              have hlrn_true : kittenClauseIsLrn ks0 cid'.toNat = true := by
                have h1 : kittenClauseIsLrn st2 cid'.toNat = true := by
                  unfold kittenClauseIsLrn kittenClauseMeta; simpa [bne_iff_ne] using hlrn_c
                rw [(hrel2.clause_fields cid'.toNat).2.2.1] at h1; exact h1
              have hge_orig : ks0.orig_nc.toNat ≤ cid'.toNat := by
                have := hwf_c.1; rw [hlrn_true] at this
                exact of_decide_eq_true this.symm
              c0_hsteps_nogrp
              let off := st2.clOff[cid'.toNat]?.getD 0#32
              let sz := mval &&& 0xFFFF#32
              let na := st2.clAux[cid'.toNat]?.getD 0#32
              have hoff_eq : off.toNat = kittenClauseOff ks0 cid'.toNat := by
                have e_co : st2.clOff = ks0.clOff := by rw [hrel2.eq_with]
                simp only [off, kittenClauseOff, e_co]
              have hsz_eq : sz.toNat = kittenClauseSize ks0 cid'.toNat := by
                have h1 := (hrel2.bits_eq cid'.toNat).1
                simp only [sz, mval, kittenClauseSize, kittenClauseMeta, h1]
              have hna_eq : na.toNat = kittenClauseAux ks0 cid'.toNat := by
                have e_ca : st2.clAux = ks0.clAux := by rw [hrel2.eq_with]
                simp only [na, kittenClauseAux, e_ca]
              have hspan_le : off.toNat + sz.toNat + na.toNat ≤ acap := by
                have hsp := hwf_c.2.2.1; unfold kittenClauseSpan at hsp
                simp only [hlrn_true, ite_true] at hsp; omega
              have hants_ok := hwf_c.2.2.2.2.2 hante hge_orig
              refine wp_while_state1 (fun p : BitVec 32 × KittenState => p.1)
                (fun p => na.toNat - p.1.toNat)
                (fun p m4 => p.1.toNat ≤ na.toNat ∧ CoreMetaRelM5 ks0 p.2 ∧
                  (cnfOfClauses (coreMarkedClausesM5 p.2 ks0.nc.toNat) ++
                    unitsCnf (kittenAssumpLits ks0)).Unsat ∧
                  (∀ c < ks0.nc.toNat, (kittenClauseMeta st2 c &&& kmCore) ≠ 0#32 →
                    (kittenClauseMeta p.2 c &&& kmCore) ≠ 0#32) ∧
                  (∀ c, cid'.toNat ≤ c → p.2.clMeta[c]? = st2.clMeta[c]?) ∧
                  (∀ t < p.1.toNat,
                    (kittenClauseMeta p.2
                      (ks0.arena[off.toNat + sz.toNat + t]?.getD 0#32).toNat &&& kmCore) ≠ 0#32) ∧
                  (KittenMemA kPtr acap p.2 ⋆ (FullKittenFrame c s ⋆ R)) m4)
                ?_ ?_
              · intro J4 hJ4
                exact wp_jump_state (proj := fun p : BitVec 32 × KittenState => (p.1, ()))
                  (0#32, st2) rfl
                  (hJ4 _ m2 ⟨by simp, hrel2, huns2, fun _ _ h => h, fun _ _ => rfl,
                    fun _ h => by simp at h, hm2⟩)
              · rintro J4 ⟨j, st4⟩ m4 ⟨hj_le, hrel4, huns4, hmono4, hhi4, hmarked4, hm4⟩ ih4
                dsimp only at hj_le hrel4 huns4 hmono4 hhi4 hmarked4 hm4
                have hsub_comm :
                    (2 ^ 32 - BitVec.toNat (1 : BitVec 32) + cid.toNat) % 2 ^ 32 = cid'.toNat := by
                  dsimp only [cid']; bv_omega
                c0_hsplit
                · have hj_lt : j.toNat < na.toNat := by dsimp only [na]; rwa [hsub_comm] at hc
                  have hidx_lt : off.toNat + sz.toNat + j.toNat < acap := by omega
                  have hidx_wrap : off.toNat + sz.toNat + j.toNat < 2 ^ 28 := by omega
                  c0_hstep; c0_hstep; c0_hstep; c0_hstep; c0_hstep; c0_hstep
                  refine head_wp_load rfl
                    (KittenMemATactics.load_ka_arena_off2 hidx_wrap hidx_lt hm4) ?_
                  let ant := st4.arena[off.toNat + sz.toNat + j.toNat]?.getD 0#32
                  have hant_eq : ant = ks0.arena[off.toNat + sz.toNat + j.toNat]?.getD 0#32 := by
                    have e_ar : st4.arena = ks0.arena := by rw [hrel4.eq_with]
                    simp only [ant, e_ar]
                  have hant_mem : ant.toNat ∈ kittenClauseAnts ks0 cid'.toNat := by
                    unfold kittenClauseAnts; simp only [hlrn_true, ite_true, List.mem_map]
                    have har_lt : off.toNat + sz.toNat + j.toNat < ks0.arena.length := by
                      rw [hsh0.arena_len]; exact hidx_lt
                    refine ⟨ks0.arena[off.toNat + sz.toNat + j.toNat]'har_lt, ?_, ?_⟩
                    · rw [List.mem_iff_getElem]
                      exact ⟨j.toNat, by
                          simp only [List.length_take, List.length_drop, hsh0.arena_len,
                            ← hoff_eq, ← hsz_eq, ← hna_eq]; omega,
                        by simp only [List.getElem_take, List.getElem_drop, ← hoff_eq, ← hsz_eq]⟩
                    · rw [hant_eq, List.getElem?_eq_getElem har_lt, Option.getD_some]
                  have hant_lt_c : ant.toNat < cid'.toNat := hants_ok.1 _ hant_mem
                  have hant_lt_nc : ant.toNat < ks0.nc.toNat := Nat.lt_trans hant_lt_c hcid'_lt
                  have hant_896 : ant.toNat < 896 := by unfold kMaxCl at hnc; omega
                  have hant_wrap : ant.toNat < 2 ^ 28 := by omega
                  have hj1 : (j + 1#32).toNat = j.toNat + 1 := by bv_omega
                  c0_hsteps!
                  · let st4' := st4.putArr .clMeta ant.toNat
                      (st4.clMeta[ant.toNat]?.getD 0#32 ||| kmCore)
                    refine ih4 (j + 1#32, st4') _ (by dsimp only; rw [hj1]; omega)
                      ⟨by dsimp only; rw [hj1]; omega, hrel4.setCore ant.toNat hant_896,
                        coreMarkedM5_setCore_unsat hrel4 hant_896 huns4, ?_, ?_, ?_, hm⟩
                    · intro cl hcl hcm2
                      have hcm4 := hmono4 cl hcl hcm2
                      by_cases hca : cl = ant.toNat
                      · have hlt : ant.toNat < st4.clMeta.length := by
                          rw [hrel4.clMeta_len]; exact hant_896
                        change ((st4.clMeta.set ant.toNat _)[cl]?.getD 0#32 &&& kmCore) ≠ 0#32
                        rw [hca, List.getElem?_set_self hlt, Option.getD_some]
                        exact bv32_and_core_or_core _
                      · change ((st4.clMeta.set ant.toNat _)[cl]?.getD 0#32 &&& kmCore) ≠ 0#32
                        rw [List.getElem?_set_ne (Ne.symm hca)]; exact hcm4
                    · intro cl hcl_ge
                      change (st4.clMeta.set ant.toNat _)[cl]? = st2.clMeta[cl]?
                      rw [List.getElem?_set_ne (by omega)]; exact hhi4 cl hcl_ge
                    · intro t ht
                      rw [hj1] at ht
                      by_cases htj : t = j.toNat
                      · subst htj
                        have hlt : ant.toNat < st4.clMeta.length := by
                          rw [hrel4.clMeta_len]; exact hant_896
                        rw [← hant_eq]
                        change ((st4.clMeta.set ant.toNat _)[ant.toNat]?.getD 0#32 &&& kmCore) ≠
                          0#32
                        rw [List.getElem?_set_self hlt, Option.getD_some]
                        exact bv32_and_core_or_core _
                      · have hprev := hmarked4 t (by omega)
                        let idx := (ks0.arena[off.toNat + sz.toNat + t]?.getD 0#32).toNat
                        by_cases hia : idx = ant.toNat
                        · have hlt : ant.toNat < st4.clMeta.length := by
                            rw [hrel4.clMeta_len]; exact hant_896
                          change ((st4.clMeta.set ant.toNat _)[idx]?.getD 0#32 &&& kmCore) ≠ 0#32
                          rw [hia, List.getElem?_set_self hlt, Option.getD_some]
                          exact bv32_and_core_or_core _
                        · change ((st4.clMeta.set ant.toNat _)[idx]?.getD 0#32 &&& kmCore) ≠ 0#32
                          rw [List.getElem?_set_ne (Ne.symm hia)]; exact hprev
                  · exfalso; rw [hsub_comm] at hc; exact hc hant_lt_nc
                · have hj_eq : j.toNat = na.toNat := by
                    rw [hsub_comm] at hc; change ¬ j.toNat < na.toNat at hc; omega
                  rw [hj_eq] at hmarked4
                  c0_hsteps!
                  refine hJ3 st4 m4 ⟨hrel4, huns4, ?_, hm4⟩
                  intro c hc_ge hc_lt hcm4 hge_o a ha
                  by_cases hcc : c = cid'.toNat
                  · subst hcc
                    unfold kittenClauseAnts at ha
                    simp only [hlrn_true, ite_true, List.mem_map] at ha
                    obtain ⟨b, hb, rfl⟩ := ha
                    obtain ⟨t, ht_len, ht_eq⟩ := List.getElem_of_mem hb
                    have ht_lt : t < na.toNat := by
                      simp only [List.length_take, List.length_drop, hsh0.arena_len,
                        ← hoff_eq, ← hsz_eq, ← hna_eq] at ht_len; omega
                    have hb_eq : b = ks0.arena[off.toNat + sz.toNat + t]?.getD 0#32 := by
                      rw [← ht_eq]
                      simp only [List.getElem_take, List.getElem_drop, ← hoff_eq, ← hsz_eq]
                      rw [List.getElem?_eq_getElem (by rw [hsh0.arena_len]; omega),
                        Option.getD_some]
                    rw [hb_eq]; exact hmarked4 t ht_lt
                  · have hc_gt : cid.toNat ≤ c := by omega
                    have hcm2 : (kittenClauseMeta st2 c &&& kmCore) ≠ 0#32 := by
                      unfold kittenClauseMeta at hcm4 ⊢; rwa [hhi4 c hc_ge] at hcm4
                    exact hmono4 a
                      (Nat.lt_trans (((hcl0.cl_wf c hc_lt).2.2.2.2.2 hante hge_o).1 a ha) hc_lt)
                      (hdag2 c hc_gt hc_lt hcm2 hge_o a ha)
            · c0_hsteps!
              have hnlrn : (mval &&& kmLrn) = 0#32 := ‹_›
              refine hJ3 st2 m2 ⟨hrel2, huns2, ?_, hm2⟩
              intro c hc_ge hc_lt hcm hge_o a ha
              by_cases hcc : c = cid'.toNat
              · subst hcc; exfalso
                have h1 : kittenClauseIsLrn st2 cid'.toNat = false := by
                  unfold kittenClauseIsLrn kittenClauseMeta
                  rw [bne_eq_false_iff_eq]; exact hnlrn
                rw [(hrel2.clause_fields cid'.toNat).2.2.1, hwf_c.1] at h1
                rw [decide_eq_true hge_o] at h1; cases h1
              · exact hdag2 c (by omega) hc_lt hcm hge_o a ha
          · c0_hsteps!
            have hncore : (mval &&& kmCore) = 0#32 := ‹_›
            refine hJ3 st2 m2 ⟨hrel2, huns2, ?_, hm2⟩
            intro c hc_ge hc_lt hcm hge_o a ha
            by_cases hcc : c = cid'.toNat
            · subst hcc; exact absurd hncore hcm
            · exact hdag2 c (by omega) hc_lt hcm hge_o a ha
      · have hcid_zero : cid.toNat = 0 := by bv_omega
        rw [hcid_zero] at hdag2
        c0_hsteps_nogrp
        have honc_eq : st2.orig_nc = ks0.orig_nc := by rw [hrel2.eq_with]
        refine wp_while_state_pure (fun p : BitVec 32 × BitVec 32 => (p.1, (p.2, ())))
          (fun p => ks0.orig_nc.toNat - p.2.toNat)
          (fun p => p.2.toNat ≤ ks0.orig_nc.toNat ∧ p.1.toNat ≤ p.2.toNat)
          ?_ ?_
        · intro J3 hJ3
          exact wp_jump_state (proj := fun p : BitVec 32 × BitVec 32 => (p.1, (p.2, ())))
            (0#32, 0#32) rfl (hJ3 _ ⟨by simp, by simp⟩)
        · rintro J3 ⟨csz, i⟩ ⟨hi_le, hcsz_le⟩ ih3
          dsimp only at hi_le hcsz_le
          c0_hsplit
          · have hi_lt : i.toNat < ks0.orig_nc.toNat := by rw [honc_eq] at *; bv_omega
            have hi_896 : i.toNat < 896 := by
              have := hcl0.orig_nc_max; unfold kMaxOrig at this; omega
            have hi_wrap : i.toNat < 2 ^ 28 := by omega
            have hi1 : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
            have hcsz1 : (csz + 1#32).toNat = csz.toNat + 1 := by
              have := hcl0.orig_nc_max; unfold kMaxOrig at this; bv_omega
            c0_hsteps!
            · exact ih3 (csz + 1#32, i + 1#32) (by dsimp only; rw [hi1]; omega)
                ⟨by dsimp only; rw [hi1]; omega, by dsimp only; rw [hcsz1, hi1]; omega⟩
            · exact ih3 (csz, i + 1#32) (by dsimp only; rw [hi1]; omega)
                ⟨by dsimp only; rw [hi1]; omega, by dsimp only; rw [hi1]; omega⟩
          · c0_hsteps!
            have hdag_full : ∀ c < ks0.nc.toNat, (kittenClauseMeta st2 c &&& kmCore) ≠ 0#32 →
                ks0.orig_nc.toNat ≤ c →
                ∀ a ∈ kittenClauseAnts ks0 c, (kittenClauseMeta st2 a &&& kmCore) ≠ 0#32 :=
              fun c hc => hdag2 c (Nat.zero_le c) hc
            have hsh2 := hrel2.shapes hsh0
            have hinv2 := hrel2.toInv hinv (fun _ => by
              rw [show st2.nc = ks0.nc by rw [hrel2.eq_with], hrel2.assump_eq]; exact huns2)
            have hcore_unsat := coreM5_dag_unsat hinv hrel2 hante huns2 hdag_full
            obtain ⟨_, hm2'⟩ := kittenMemA_to_mem hm2
            have hm2'_exp :
                (FullKittenFrame c s ⋆ KittenMem (c.pScratchBuf + 1024#64) st2 ⋆ R) m2 := by
              dsimp only [kPtr] at hm2'; rw [kPtr_base_eq] at hm2'; exact sep_ac hm2'
            have hmJ := fullMem_join_kitten (c := c) (s := s) (acap := acap) (ks' := st2)
              (R := R) (by change 256 ≤ scr.length; omega) hsh2 hm2'_exp
            let scr' := s.scratch.scratch_buf.take 256 ++ st2.toSlab
            have hscr_s_eq : s.scratch.scratch_buf = scr := rfl
            have hscr'_len : scr'.length = c.scratch_cap := by
              simp only [scr', hscr_s_eq, List.length_append,
                List.length_take_of_le (by omega : 256 ≤ scr.length),
                KittenState.toSlab_length hsh2]
              dsimp only [acap]; omega
            have hpre : ∀ x < kBase, scr'[x]? = s.scratch.scratch_buf[x]? := by
              intro x hx
              have htk : x < (s.scratch.scratch_buf.take 256).length := by
                rw [hscr_s_eq, List.length_take_of_le (by omega : 256 ≤ scr.length)]
                unfold kBase at hx; omega
              rw [List.getElem?_append_left htk, List.getElem?_take_of_lt
                (by unfold kBase at hx; omega)]
            have hof : kittenStateOfScratch scr' = st2 := by
              unfold kittenStateOfScratch
              rw [slab_drop_exact _ st2.toSlab (by
                rw [hscr_s_eq, List.length_take_of_le (by omega : 256 ≤ scr.length)])]
              exact KittenState.ofSlab_toSlab hsh2
            have hks_inv : KittenScratchInv scr' := by
              refine ⟨by omega, by rw [hscr'_len]; exact c.hscr, ?_⟩
              rw [hof, show scr'.length - 8864 = acap by dsimp only [acap]; omega]
              exact hinv2
            exact hQ csz scr' m2 (fullState_lengthsOk_scratch hlen hscr'_len) hpre hks_inv
              (by rw [hof, honc_eq]; omega)
              (by rw [hof, hrel2.eq_with]) (by rw [hof, honc_eq])
              (by rw [hof, hrel2.eq_with]) (by rw [hof, hrel2.eq_with])
              (by rw [hof, hrel2.eq_with]) (by rw [hof, hrel2.eq_with])
              (by unfold kittenOrigClausesS; rw [hof]; exact hrel2.orig_eq)
              (by unfold kittenAssumpLitsS; rw [hof]; exact hrel2.assump_eq)
              (by intro ci _; rw [hof, hrel2.eq_with])
              (by unfold kittenCoreClausesS kittenOrigClausesS; rw [hof]
                  exact mem_kittenCoreClausesM5_orig st2)
              (by unfold kittenCoreClausesS kittenAssumpLitsS; rw [hof]; exact hcore_unsat)
              hmJ
  · intro J1 hJ1
    c0_hsplit
    · -- `k[KH_INCONS] != 0xFFFFFFFFu`: clear `KM_CORE` on `0..nc` and seed `incons` + lvl-0 rsns
      have hinc_ne : ks0.incons ≠ 0xFFFFFFFF#32 := ‹_›
      c0_hsteps_nogrp
      refine wp_while_state1 (fun p : BitVec 32 × KittenState => p.1)
        (fun p => ks0.nc.toNat - p.1.toNat)
        (fun p m1 => p.1.toNat ≤ ks0.nc.toNat ∧ CoreMetaRelM5 ks0 p.2 ∧
          (KittenMemA kPtr acap p.2 ⋆ (FullKittenFrame c s ⋆ R)) m1)
        ?_ ?_
      · intro J2 hJ2
        exact wp_jump_state (proj := fun p : BitVec 32 × KittenState => (p.1, ()))
          (0#32, ks0) rfl (hJ2 _ m ⟨by simp, CoreMetaRelM5.refl hsh0, hmA⟩)
      · rintro J2 ⟨i, st⟩ m1 ⟨hi_le, hrel, hm1⟩ ih
        dsimp only at hi_le hrel hm1
        c0_hsplit
        · have hi_lt : i.toNat < ks0.nc.toNat := by bv_omega
          have hi_896 : i.toNat < 896 := by unfold kMaxCl at hnc; omega
          have hi_wrap : i.toNat < 2 ^ 28 := by omega
          have hi1 : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
          c0_hsteps!
          exact ih (i + 1#32, _) _ (by dsimp only; rw [hi1]; omega)
            ⟨by dsimp only; rw [hi1]; omega, hrel.clearCore i.toNat hi_896, hm⟩
        · have hinc_eq : st.incons = ks0.incons := by rw [hrel.eq_with]
          have hio := hcl0.incons_ok hinc_ne
          have hinc_896 : ks0.incons.toNat < 896 := by
            have := hio.1; unfold kMaxCl at hnc; omega
          have hinc_wrap : ks0.incons.toNat < 2 ^ 28 := by omega
          have hinc_st_896 : st.incons.toNat < 896 := by rw [hinc_eq]; exact hinc_896
          have hinc_st_wrap : st.incons.toNat < 2 ^ 28 := by rw [hinc_eq]; exact hinc_wrap
          c0_hsteps_nogrp
          let stI := st.putArr .clMeta st.incons.toNat
            (st.clMeta[st.incons.toNat]?.getD 0#32 ||| kmCore)
          have hrelI : CoreMetaRelM5 ks0 stI := hrel.setCore st.incons.toNat hinc_st_896
          have hmarkI : (kittenClauseMeta stI ks0.incons.toNat &&& kmCore) ≠ 0#32 := by
            have hlt : st.incons.toNat < st.clMeta.length := by
              rw [hrel.clMeta_len]; exact hinc_st_896
            change ((st.clMeta.set st.incons.toNat _)[ks0.incons.toNat]?.getD 0#32 &&&
              kmCore) ≠ 0#32
            rw [← hinc_eq, List.getElem?_set_self hlt, Option.getD_some]
            exact bv32_and_core_or_core _
          let off := stI.clOff[st.incons.toNat]?.getD 0#32
          let sz := stI.clMeta[st.incons.toNat]?.getD 0#32 &&& 0xFFFF#32
          have hoff_eq : off.toNat = kittenClauseOff ks0 ks0.incons.toNat := by
            have e_co : stI.clOff = ks0.clOff := by rw [hrelI.eq_with]
            simp only [off, kittenClauseOff, e_co, hinc_eq]
          have hsz_eq : sz.toNat = kittenClauseSize ks0 ks0.incons.toNat := by
            have h1 := (hrelI.bits_eq ks0.incons.toNat).1
            simp only [sz, kittenClauseSize, kittenClauseMeta, hinc_eq, h1]
          have hwf_inc := hcl0.cl_wf ks0.incons.toNat hio.1
          have hspan_inc : off.toNat + sz.toNat ≤ acap := by
            have h1 := hwf_inc.2.2.1; unfold kittenClauseSpan at h1; omega
          refine wp_while_state1 (fun p : BitVec 32 × KittenState => p.1)
            (fun p => sz.toNat - p.1.toNat)
            (fun p m2 => p.1.toNat ≤ sz.toNat ∧ CoreMetaRelM5 ks0 p.2 ∧
              (kittenClauseMeta p.2 ks0.incons.toNat &&& kmCore) ≠ 0#32 ∧
              (∀ t < p.1.toNat,
                let l := (ks0.arena[off.toNat + t]?.getD 0#32).toNat
                let r0 := (ks0.rsn[l / 2]?.getD 0#32).toNat
                (kittenClauseMeta p.2 r0 &&& kmCore) ≠ 0#32) ∧
              (KittenMemA kPtr acap p.2 ⋆ (FullKittenFrame c s ⋆ R)) m2)
            ?_ ?_
          · intro J3 hJ3
            exact wp_jump_state (proj := fun p : BitVec 32 × KittenState => (p.1, ()))
              (0#32, stI) rfl
              (hJ3 _ _ ⟨by simp, hrelI, hmarkI, fun _ h => by simp at h, hm⟩)
          · rintro J3 ⟨j, stJ⟩ m2 ⟨hj_le, hrelJ, hmarkJ, hrsnJ, hm2⟩ ihJ
            dsimp only at hj_le hrelJ hmarkJ hrsnJ hm2
            c0_hsplit
            · have hj_lt : j.toNat < sz.toNat := by change j.toNat < sz.toNat at hc; exact hc
              have hidx_lt : off.toNat + j.toNat < acap := by omega
              have hidx_wrap : off.toNat + j.toNat < 2 ^ 28 := by omega
              let lit := stJ.arena[off.toNat + j.toNat]?.getD 0#32
              have hlit_eq : lit = ks0.arena[off.toNat + j.toNat]?.getD 0#32 := by
                have e_ar : stJ.arena = ks0.arena := by rw [hrelJ.eq_with]
                simp only [lit, e_ar]
              have hlit_mem : lit.toNat ∈ kittenClauseLits ks0 ks0.incons.toNat := by
                unfold kittenClauseLits; rw [List.mem_map]
                have har_lt : off.toNat + j.toNat < ks0.arena.length := by
                  rw [hsh0.arena_len]; exact hidx_lt
                refine ⟨ks0.arena[off.toNat + j.toNat]'har_lt, ?_, ?_⟩
                · rw [List.mem_iff_getElem]
                  exact ⟨j.toNat,
                    by simp only [List.length_take, List.length_drop, hsh0.arena_len,
                         ← hoff_eq, ← hsz_eq]; omega,
                    by simp only [List.getElem_take, List.getElem_drop, ← hoff_eq]⟩
                · rw [hlit_eq, List.getElem?_eq_getElem har_lt, Option.getD_some]
              have hlit_lt : lit.toNat < 2 * ks0.nv.toNat := hwf_inc.2.2.2.1 _ hlit_mem
              obtain ⟨hv_eq, hv_lt⟩ := bv32_lit_div2_bv hlit_lt
              have hv_128 : (lit >>> (1 : Nat)).toNat < 128 := by unfold kMaxV at hnv; omega
              have hv_wrap : (lit >>> (1 : Nat)).toNat < 2 ^ 28 := by omega
              c0_hstep; c0_hstep; c0_hstep; c0_hstep; c0_hstep
              refine head_wp_load rfl
                (KittenMemATactics.load_ka_arena_off hidx_wrap hidx_lt hm2) ?_
              c0_hsteps_nogrp
              let r0 := stJ.rsn[(lit >>> (1 : Nat)).toNat]?.getD 0#32
              have hr0_eq : r0 = ks0.rsn[lit.toNat / 2]?.getD 0#32 := by
                have e_rs : stJ.rsn = ks0.rsn := by rw [hrelJ.eq_with]
                simp only [r0, hv_eq, e_rs]
              have hr0_ok := (hio.2.2 lit.toNat hlit_mem).2.2 hante; dsimp only at hr0_ok
              have hrs_len : lit.toNat / 2 < ks0.rsn.length := by
                rw [hsh0.rsn_len]; unfold kMaxV at hnv; omega
              have hr0_toNat : r0.toNat < ks0.nc.toNat := by
                rw [hr0_eq, List.getElem?_eq_getElem hrs_len, Option.getD_some]
                have h1 := hr0_ok.1; rwa [List.getElem?_eq_getElem hrs_len, Option.getD_some] at h1
              have hr0_896 : r0.toNat < 896 := by unfold kMaxCl at hnc; omega
              have hr0_wrap : r0.toNat < 2 ^ 28 := by omega
              have hj1 : (j + 1#32).toNat = j.toNat + 1 := by bv_omega
              c0_hsteps!
              · let stJ' := stJ.putArr .clMeta r0.toNat
                  (stJ.clMeta[r0.toNat]?.getD 0#32 ||| kmCore)
                refine ihJ (j + 1#32, stJ') _ (by dsimp only; rw [hj1]; omega)
                  ⟨by dsimp only; rw [hj1]; omega, hrelJ.setCore r0.toNat hr0_896, ?_, ?_, hm⟩
                · by_cases hi_r : ks0.incons.toNat = r0.toNat
                  · have hlt : r0.toNat < stJ.clMeta.length := by
                      rw [hrelJ.clMeta_len]; exact hr0_896
                    change ((stJ.clMeta.set r0.toNat _)[ks0.incons.toNat]?.getD 0#32 &&&
                      kmCore) ≠ 0#32
                    rw [hi_r, List.getElem?_set_self hlt, Option.getD_some]
                    exact bv32_and_core_or_core _
                  · change ((stJ.clMeta.set r0.toNat _)[ks0.incons.toNat]?.getD 0#32 &&&
                      kmCore) ≠ 0#32
                    rw [List.getElem?_set_ne (Ne.symm hi_r)]; exact hmarkJ
                · intro t ht
                  rw [hj1] at ht
                  by_cases htj : t = j.toNat
                  · subst htj; dsimp only; rw [← hlit_eq, ← hr0_eq]
                    have hlt : r0.toNat < stJ.clMeta.length := by
                      rw [hrelJ.clMeta_len]; exact hr0_896
                    change ((stJ.clMeta.set r0.toNat _)[r0.toNat]?.getD 0#32 &&& kmCore) ≠ 0#32
                    rw [List.getElem?_set_self hlt, Option.getD_some]
                    exact bv32_and_core_or_core _
                  · have hprev := hrsnJ t (by omega); dsimp only at hprev ⊢
                    let idx := (ks0.rsn[(ks0.arena[off.toNat + t]?.getD 0#32).toNat / 2]?.getD
                      0#32).toNat
                    by_cases hir : idx = r0.toNat
                    · have hlt : r0.toNat < stJ.clMeta.length := by
                        rw [hrelJ.clMeta_len]; exact hr0_896
                      change ((stJ.clMeta.set r0.toNat _)[idx]?.getD 0#32 &&& kmCore) ≠ 0#32
                      rw [hir, List.getElem?_set_self hlt, Option.getD_some]
                      exact bv32_and_core_or_core _
                    · change ((stJ.clMeta.set r0.toNat _)[idx]?.getD 0#32 &&& kmCore) ≠ 0#32
                      rw [List.getElem?_set_ne (Ne.symm hir)]; exact hprev
              · exfalso
                have hff : r0 = 0xFFFFFFFF#32 := by dsimp only [r0]; rw [hv_eq]; exact hc
                have : r0.toNat = 2 ^ 32 - 1 := by rw [hff]; decide
                omega
            · have hj_eq : j.toNat = sz.toNat := by change ¬ j.toNat < sz.toNat at hc; omega
              rw [hj_eq] at hrsnJ
              c0_hsteps!
              refine hJ1 stJ m2 ⟨hrelJ, ?_, hm2⟩
              refine coreM5_incons_seeded_unsat hinv hrelJ hante hinc_ne hmarkJ fun t ht => ?_
              rw [← hoff_eq]; exact hrsnJ t (hsz_eq ▸ ht)
    · -- `k[KH_INCONS] == 0xFFFFFFFFu`: `FAILING` path (already freshly cleared + seeded!)
      c0_hsteps!
      have hinc_ff : ks0.incons = 0xFFFFFFFF#32 := ‹_›
      have hfail_ne : ks0.failing ≠ 0xFFFFFFFF#32 := hor_if.resolve_left (fun h => h hinc_ff)
      exact hJ1 ks0 m ⟨CoreMetaRelM5.refl hsh0, hcl0.failing_ok hante hfail_ne, hmA⟩

/-! ## 5. `full_kitten_solve_m5_wp` (`Full.fullKittenSolveSpec`) -/

private theorem mem_kittenAssumpLits_of_lt_m5 {ks : KittenState}
    (hlen : ks.nassump.toNat ≤ ks.assump.length) {i : Nat} (hi : i < ks.nassump.toNat) :
    (ks.assump[i]?.getD 0#32).toNat ∈ kittenAssumpLits ks := by
  unfold kittenAssumpLits; rw [List.mem_map]
  refine ⟨ks.assump[i]'(by omega), ?_, ?_⟩
  · rw [List.mem_take_iff_getElem]; exact ⟨i, by omega, rfl⟩
  · simp [List.getElem?_eq_getElem (by omega : i < ks.assump.length)]

private theorem bv32_shl1_or_bit_m5 {pick ph : BitVec 32} {nv : Nat}
    (hp : pick.toNat < nv) (hnv : nv ≤ kMaxV) (hph : ph.toNat < 2) :
    ((pick <<< (1 : Nat)) ||| ph).toNat = 2 * pick.toNat + ph.toNat ∧
    ((pick <<< (1 : Nat)) ||| ph).toNat < 2 * nv := by
  unfold kMaxV at hnv
  have hshl : (pick <<< (1 : Nat)).toNat = 2 * pick.toNat := by
    rw [BitVec.toNat_shiftLeft]; simp; omega
  have h1 : ((pick <<< (1 : Nat)) ||| ph).toNat = 2 * pick.toNat + ph.toNat := by
    rw [BitVec.toNat_or, hshl]
    rcases (by omega : ph.toNat = 0 ∨ ph.toNat = 1) with h0 | h1
    · rw [h0]; simp
    · rw [h1]
      apply Nat.eq_of_testBit_eq; intro k; rw [Nat.testBit_or]
      cases k with
      | zero => simp [Nat.testBit_zero]
      | succ k => simp [Nat.testBit_succ, show (2 * pick.toNat + 1) / 2 = pick.toNat by omega]
  exact ⟨h1, by omega⟩

private theorem solve_m5_post_finish {c : FullCfg} {s : FullState} {scr : List (BitVec 32)}
    {ks0 ks' : KittenState} {R : Mem 64 → Prop} {Q : Post [i64]}
    {r fuel' : BitVec 64} {m' : Mem 64}
    (hlen : s.LengthsOk c) (h256 : 256 ≤ scr.length) (hscr_len : scr.length = c.scratch_cap)
    (hscr_ge : kMinScratchCap ≤ scr.length) (hof_ks0 : kittenStateOfScratch scr = ks0)
    (hinv' : ks'.Inv (scr.length - 8864)) (hfuel : fuel'.toNat ≤ s.core.fuel.toNat)
    (e_nv : ks'.nv = ks0.nv) (e_on : ks'.orig_nc = ks0.orig_nc)
    (e_ant : ks'.ante = ks0.ante) (e_na : ks'.nassump = ks0.nassump)
    (e_ass : ks'.assump = ks0.assump)
    (hperm : KittenCnfPermEquiv (kittenOrigClauses ks') (kittenOrigClauses ks0))
    (hclAux : ∀ ci < ks0.orig_nc.toNat, ks'.clAux[ci]? = ks0.clAux[ci]?)
    (hcore : r ≠ 20#64 → ∀ ci < ks0.orig_nc.toNat,
      (ks'.clMeta[ci]?.getD 0#32 &&& kmCore) = (ks0.clMeta[ci]?.getD 0#32 &&& kmCore))
    (hr : r = 0#64 ∨ r = 10#64 ∨ r = 20#64)
    (hr20 : r = 20#64 → (ks'.incons ≠ 0xFFFFFFFF#32 ∨ ks'.failing ≠ 0xFFFFFFFF#32) ∧
      (cnfOfClauses (kittenOrigClauses ks') ++ unitsCnf (kittenAssumpLits ks')).Unsat)
    (hm' : (FullKittenFrame c { s with core := { s.core with fuel := fuel' } } ⋆
      KittenMem (c.pScratchBuf + 1024#64) ks' ⋆ R) m')
    (hQ : ∀ (r fuel' : BitVec 64) (scr' : List (BitVec 32)) (m' : Mem 64),
      let s' : FullState :=
        { s with core := { s.core with fuel := fuel' }
                 scratch := { s.scratch with scratch_buf := scr' } }
      let ks := kittenStateOfScratch s.scratch.scratch_buf
      let ks' := kittenStateOfScratch scr'
      s'.LengthsOk c → fuel'.toNat ≤ s.core.fuel.toNat →
      (∀ i < kBase, scr'[i]? = s.scratch.scratch_buf[i]?) → KittenScratchInv scr' →
      ks'.nv = ks.nv → ks'.orig_nc = ks.orig_nc → ks'.ante = ks.ante →
      ks'.nassump = ks.nassump →
      kittenAssumpLitsS scr' = kittenAssumpLitsS s.scratch.scratch_buf →
      KittenCnfPermEquiv (kittenOrigClausesS scr') (kittenOrigClausesS s.scratch.scratch_buf) →
      (∀ ci < ks.orig_nc.toNat, ks'.clAux[ci]? = ks.clAux[ci]?) →
      (r ≠ 20#64 → ∀ ci < ks.orig_nc.toNat,
        (ks'.clMeta[ci]?.getD 0#32 &&& kmCore) = (ks.clMeta[ci]?.getD 0#32 &&& kmCore)) →
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
      (r = 20#64 → (ks'.incons ≠ 0xFFFFFFFF#32 ∨ ks'.failing ≠ 0xFFFFFFFF#32) ∧
        (cnfOfClauses (kittenOrigClausesS scr') ++ unitsCnf (kittenAssumpLitsS scr')).Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m')
    (hscr_eq : s.scratch.scratch_buf = scr) :
    Q (r, ()) m' := by
  let sFuel : FullState := { s with core := { s.core with fuel := fuel' } }
  let scr' := scr.take 256 ++ ks'.toSlab
  have hsh' := hinv'.shapes
  have hscr'_len : scr'.length = c.scratch_cap := by
    simp only [scr', List.length_append, List.length_take_of_le h256,
      KittenState.toSlab_length hsh']
    unfold kMinScratchCap at hscr_ge; omega
  have hpre : ∀ x < kBase, scr'[x]? = s.scratch.scratch_buf[x]? := by
    intro x hx; rw [hscr_eq]
    rw [List.getElem?_append_left (by rw [List.length_take_of_le h256]; unfold kBase at hx; omega),
      List.getElem?_take_of_lt (by unfold kBase at hx; omega)]
  have hof' : kittenStateOfScratch scr' = ks' := by
    unfold kittenStateOfScratch
    rw [slab_drop_exact _ ks'.toSlab (by rw [List.length_take_of_le h256])]
    exact KittenState.ofSlab_toSlab hsh'
  have hks_inv' : KittenScratchInv scr' := by
    refine ⟨by rw [hscr'_len, ← hscr_len]; exact hscr_ge, by rw [hscr'_len]; exact c.hscr, ?_⟩
    rw [hof', hscr'_len, ← hscr_len]; exact hinv'
  have hlen_f : sFuel.LengthsOk c :=
    ⟨{ hlen.core_ok with }, hlen.scratch_ok⟩
  have hlen' : FullState.LengthsOk c
      { sFuel with scratch := { s.scratch with scratch_buf := scr' } } :=
    fullState_lengthsOk_scratch hlen_f (by rw [hscr'_len])
  have hm_join := fullMem_join_kitten (c := c) (s := sFuel) (acap := scr.length - 8864)
    (ks' := ks') (R := R)
    (by change 256 ≤ sFuel.scratch.scratch_buf.length; rw [hscr_eq]; exact h256)
    hsh' hm'
  refine hQ r fuel' scr' m' hlen' hfuel hpre hks_inv'
    (by rw [hof', hscr_eq, hof_ks0]; exact e_nv)
    (by rw [hof', hscr_eq, hof_ks0]; exact e_on)
    (by rw [hof', hscr_eq, hof_ks0]; exact e_ant)
    (by rw [hof', hscr_eq, hof_ks0]; exact e_na)
    (by unfold kittenAssumpLitsS kittenAssumpLits; rw [hof', hscr_eq, hof_ks0, e_na, e_ass])
    (by unfold kittenOrigClausesS; rw [hof', hscr_eq, hof_ks0]; exact hperm)
    (by rw [hof', hscr_eq, hof_ks0]; exact hclAux)
    (fun hne => by rw [hof', hscr_eq, hof_ks0]; exact hcore hne)
    hr (fun h20 => by unfold kittenOrigClausesS kittenAssumpLitsS; rw [hof']; exact hr20 h20)
    (by simpa [sFuel, scr', hscr_eq] using hm_join)

/-- Parametric `Func.wp` proof for `full_kitten_solve_m5` (saturating `TICK_LIM` + strict `<`). -/
theorem full_kitten_solve_m5_wp (Γ : Env)
    (hBt : ∀ args m Q X, fullKittenBacktrackSpec args m Q X →
      Γ "full_kitten_backtrack" [i64, i32] [] args m Q X)
    (hAsg : ∀ args m Q X, fullKittenAssignSpec args m Q X →
      Γ "full_kitten_assign" [i64, i32, i32] [] args m Q X)
    (hProp : ∀ args m Q X, fullKittenPropagateSpec args m Q X →
      Γ "full_kitten_propagate" [i64] [i32] args m Q X)
    (hAna : ∀ args m Q X, fullKittenAnalyzeSpec args m Q X →
      Γ "full_kitten_analyze" [i64, i32] [.bool] args m Q X)
    (hBf : ∀ args m Q X, fullKittenBuildFailingSpec args m Q X →
      Γ "full_kitten_build_failing_m5" [i64, i32] [] args m Q X) :
    ∀ args m Q X, fullKittenSolveSpec args m Q X →
      Func.wp Γ full_kitten_solve_m5_body args m Q X := by
  rintro ⟨hPtr, tick_lim, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hscr_inv, hm, hQ⟩
  rcases hscr_inv with ⟨hscr_ge, hscr_lt, hinv0⟩
  let scr := s.scratch.scratch_buf
  let acap := scr.length - 8864
  let ks0 := kittenStateOfScratch scr
  have hscr_len : scr.length = c.scratch_cap := hlen.scratch_ok.scratch_buf_len
  have hscr_8864 : 8864 ≤ scr.length := by
    dsimp only [scr]; unfold kMinScratchCap at hscr_ge; omega
  have h256 : 256 ≤ scr.length := by omega
  let kPtr := c.pScratchBuf + BitVec.ofNat 64 256 * 4
  have hkPtr_eq : kPtr = c.pScratchBuf + 1024#64 := kPtr_base_eq c.pScratchBuf
  have hmF0 : (FullKittenFrame c s ⋆ KittenMem kPtr ks0 ⋆ R) m := by
    rw [fullMem_eq_kittenFrame hscr_8864] at hm; rw [hkPtr_eq]; exact sep_ac hm
  clear hm
  c0_hsteps_nogrp
  c0_hcall hBt
  · refine ⟨acap, ks0, FullKittenFrame c s ⋆ R, hinv0, fun i hi hle => ?_, sep_ac hmF0, ?_⟩
    · have hl0 : ks0.lvlArr[(ks0.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 = 0#32 :=
        BitVec.eq_of_toNat_eq (Nat.eq_zero_of_le_zero hle)
      have h0 := hinv0.assign.lvl0_ok i hi hl0
      exact ⟨h0.2.1, h0.2.2.1⟩
    · intro ks1 m1 hinv1 hsync1 hlvl1 _ _ hbt1 _ _ hm1
      have hframe1 : SolveFrame ks0 ks1 :=
        ⟨hbt1.nv, hbt1.orig_nc, hbt1.ante, hbt1.nassump, hbt1.assump, by
          rw [kittenOrigClauses_eq_of hbt1.orig_nc fun ci _ => by
            simp [kittenClauseLits, kittenClauseOff, kittenClauseSize, kittenClauseMeta,
              hbt1.clOff, hbt1.clMeta, hbt1.arena]]
          exact KittenCnfPermEquiv.refl _,
         fun ci _ => by rw [hbt1.clAux],
         fun ci _ => by rw [hbt1.clMeta]⟩
      have hmA1 : (KittenMemA kPtr acap ks1 ⋆ (FullKittenFrame c s ⋆ R)) m1 :=
        kittenMem_to_amem hinv1.shapes (sep_ac hm1)
      clear hm1
      c0_hsplit
      · have hinc1 : ks1.incons ≠ 0xFFFFFFFF#32 := ‹_›
        c0_hsteps!
        have hinv1f := inv_set_failing_none hinv1
        obtain ⟨_, hmFin1⟩ := kittenMemA_to_mem hm
        have huns1 := cnfOfClauses_unsat_append_left
          (unitsCnf (kittenAssumpLits (ks1.putHdr .failing 0xFFFFFFFF#32)))
          (hinv1f.clauses.incons_ok hinc1).2.1
        refine solve_m5_post_finish hlen h256 hscr_len hscr_ge rfl hinv1f (le_refl _)
          hframe1.nv hframe1.orig_nc hframe1.ante hframe1.nassump hframe1.assump
          hframe1.perm hframe1.clAux (fun _ => hframe1.core) (Or.inr (Or.inr rfl))
          (fun _ => ⟨Or.inl hinc1, huns1⟩) ?_ hQ rfl
        rw [← hkPtr_eq]; exact sep_ac hmFin1
      · have hinc1 : ks1.incons = 0xFFFFFFFF#32 := by
          first | exact ‹_› | exact Classical.not_not.mp ‹_›
        c0_hsteps_nogrp
        refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
          (fun tlim => (tlim, ())) (fun _ => True) ?_ (fun _ hJt => by
            c0_hsplit <;> (c0_hsteps!; exact hJt _ trivial))
        rintro _ tlim _
        c0_hsteps_nogrp
        let ks2 := (ks1.putHdr .tick_lim tlim).putHdr .failing 0xFFFFFFFF#32
        have hinv2 : ks2.Inv acap := inv_set_failing_none (inv_set_tick_lim hinv1 tlim)
        have hsync2 : KittenTrailSynced ks2 := hsync1
        have hframe2 : SolveFrame ks0 ks2 := SolveFrame.trans hframe1
          ⟨rfl, rfl, rfl, rfl, rfl, KittenCnfPermEquiv.refl _, fun _ _ => rfl, fun _ _ => rfl⟩
        refine wp_while_state1 (fun p : BitVec 32 × KittenState => p.1)
          (fun p => p.2.nunits.toNat - p.1.toNat)
          (fun p m' => p.1.toNat ≤ p.2.nunits.toNat ∧ p.2.Inv acap ∧
            KittenTrailSynced p.2 ∧ p.2.lvl = 0#32 ∧ p.2.incons = 0xFFFFFFFF#32 ∧
            p.2.failing = 0xFFFFFFFF#32 ∧ SolveFrame ks0 p.2 ∧
            (KittenMemA kPtr acap p.2 ⋆ (FullKittenFrame c s ⋆ R)) m')
          ?_ ?_
        · intro J hJ
          exact wp_jump_state (proj := fun p : BitVec 32 × KittenState => (p.1, ()))
            (0#32, ks2) rfl
            (hJ _ _ ⟨by simp, hinv2, hsync2, by dsimp only [ks2]; kp_field; exact hlvl1,
              by dsimp only [ks2]; kp_field; exact hinc1, rfl, hframe2, hm⟩)
        · rintro J ⟨ui, ku⟩ m' ⟨hui_le, hinv_u, hsync_u, hlvl_u, hinc_u, hfail_u,
              hframe_u, hm_u⟩ ih_u
          try clear hm
          dsimp only at hui_le hinv_u hsync_u hlvl_u hinc_u hfail_u hframe_u hm_u
          have hnv_u := hinv_u.clauses.nv_le
          have hal_u := hinv_u.clauses.alen_le
          have hnu_le := hinv_u.clauses.nunits_le
          have hacap_lt := hinv_u.clauses.acap_lt
          c0_hsplit
          · have hui_lt : ui.toNat < ku.nunits.toNat := by bv_omega
            have hui_wrap : ui.toNat < 2 ^ 28 := by unfold kMaxL at hnu_le; omega
            have hui_256 : ui.toNat < 256 := by unfold kMaxL at hnu_le; omega
            have hui1_nat : (ui + 1#32).toNat = ui.toNat + 1 := by
              unfold kMaxL at hnu_le; bv_omega
            let ucid := ku.units[ui.toNat]?.getD 0#32
            have hucid_ok := hinv_u.clauses.units_ok ui.toNat hui_lt
            dsimp only at hucid_ok
            have hnc_u := hinv_u.clauses.nc_le
            have hucid_lt : ucid.toNat < ku.nc.toNat := hucid_ok.1
            have hucid_wrap : ucid.toNat < 2 ^ 28 := by unfold kMaxCl at hnc_u; omega
            have hucid_896 : ucid.toNat < 896 := by unfold kMaxCl at hnc_u; omega
            have hucid_wrap' : (ku.units[ui.toNat]?.getD 0#32).toNat < 2 ^ 28 := hucid_wrap
            have hucid_896' : (ku.units[ui.toNat]?.getD 0#32).toNat < 896 := hucid_896
            have hwf_u := hinv_u.clauses.cl_wf ucid.toNat hucid_ok.1
            have hoff_lt : kittenClauseOff ku ucid.toNat < acap := by
              have hsp1 : 1 ≤ kittenClauseSpan ku ucid.toNat := by
                unfold kittenClauseSpan; rw [hucid_ok.2]; omega
              omega
            have hoff_wrap : kittenClauseOff ku ucid.toNat < 2 ^ 28 := by
              unfold dimacsBound at hacap_lt; omega
            have hoff_lt' : (ku.clOff[(ku.units[ui.toNat]?.getD 0#32).toNat]?.getD 0#32).toNat <
                acap := hoff_lt
            have hoff_wrap' : (ku.clOff[(ku.units[ui.toNat]?.getD 0#32).toNat]?.getD 0#32).toNat <
                2 ^ 28 := hoff_wrap
            let ul := ku.arena[kittenClauseOff ku ucid.toNat]?.getD 0#32
            have hlits_u : kittenClauseLits ku ucid.toNat = [ul.toNat] := by
              unfold kittenClauseLits; rw [hucid_ok.2]
              have hlen_ar : ku.arena.length = acap := hinv_u.shapes.arena_len
              have hdrop : ku.arena.drop (kittenClauseOff ku ucid.toNat) =
                  ku.arena[kittenClauseOff ku ucid.toNat]'(by omega) ::
                    ku.arena.drop (kittenClauseOff ku ucid.toNat + 1) :=
                List.drop_eq_getElem_cons (by omega)
              rw [hdrop, List.take_succ_cons, List.take_zero, List.map_singleton]
              simp [ul, List.getElem?_eq_getElem (by omega : kittenClauseOff ku ucid.toNat <
                ku.arena.length)]
            have hul_lt : ul.toNat < 2 * ku.nv.toNat :=
              hwf_u.2.2.2.1 ul.toNat (by rw [hlits_u]; simp)
            have hul_wrap : ul.toNat < 2 ^ 28 := by unfold kMaxV at hnv_u; omega
            have hul_256 : ul.toNat < 256 := by unfold kMaxV at hnv_u; omega
            have hul_wrap' : (ku.arena[(ku.clOff[(ku.units[ui.toNat]?.getD
                0#32).toNat]?.getD 0#32).toNat]?.getD 0#32).toNat < 2 ^ 28 := hul_wrap
            have hul_256' : (ku.arena[(ku.clOff[(ku.units[ui.toNat]?.getD
                0#32).toNat]?.getD 0#32).toNat]?.getD 0#32).toNat < 256 := hul_256
            c0_hstep; c0_hstep; c0_hstep; c0_hstep; c0_hstep
            c0_hstep; c0_hstep; c0_hstep; c0_hstep; c0_hstep
            c0_hstep; c0_hstep; c0_hstep; c0_hstep
            refine head_wp_load rfl (KittenMemATactics.load_ka_arena hoff_wrap' hoff_lt' hm_u) ?_
            c0_hsplit
            · have huv2 : ku.vals[ul.toNat]?.getD 0#32 = 2#32 := ‹_›
              have huv2' : ku.vals[ul.toNat]? = some 2#32 := by
                have hl : ul.toNat < ku.vals.length := by rw [hinv_u.shapes.vals_len]; exact hul_256
                rw [List.getElem?_eq_getElem hl, Option.getD_some] at huv2
                rw [List.getElem?_eq_getElem hl, huv2]
              c0_hsteps!
              have hinc_ucid : ucid ≠ 0xFFFFFFFF#32 := by
                intro h; have := congrArg BitVec.toNat h
                change ucid.toNat = 2 ^ 32 - 1 at this; omega
              have hfals_u : ∀ l ∈ kittenClauseLits ku ucid.toNat, ku.vals[l]? = some 2#32 := by
                intro l hl; rw [hlits_u] at hl; simp at hl; subst hl; exact huv2'
              have ⟨hinv_i, _⟩ := inv_set_incons_lvl0 hinv_u hsync_u hlvl_u hucid_ok.1 hfals_u
              have huns_i := cnfOfClauses_unsat_append_left (unitsCnf (kittenAssumpLits (ku.putHdr
                .incons ucid))) (hinv_i.clauses.incons_ok hinc_ucid).2.1
              have hframe_i : SolveFrame ks0 (ku.putHdr .incons ucid) := SolveFrame.trans hframe_u
                ⟨rfl, rfl, rfl, rfl, rfl, KittenCnfPermEquiv.refl _, fun _ _ => rfl,
                 fun _ _ => rfl⟩
              obtain ⟨_, hmFin_i⟩ := kittenMemA_to_mem hm
              refine solve_m5_post_finish hlen h256 hscr_len hscr_ge rfl hinv_i (le_refl _)
                hframe_i.nv hframe_i.orig_nc hframe_i.ante hframe_i.nassump hframe_i.assump
                hframe_i.perm hframe_i.clAux (fun _ => hframe_i.core) (Or.inr (Or.inr rfl))
                (fun _ => ⟨Or.inl hinc_ucid, huns_i⟩) ?_ hQ rfl
              rw [← hkPtr_eq]; exact sep_ac hmFin_i
            · refine wp_join0 (fun m_j => ∃ ku' : KittenState,
                  ku'.nunits = ku.nunits ∧ ku'.Inv acap ∧ KittenTrailSynced ku' ∧
                  ku'.lvl = 0#32 ∧ ku'.incons = 0xFFFFFFFF#32 ∧
                  ku'.failing = 0xFFFFFFFF#32 ∧ SolveFrame ks0 ku' ∧
                  (KittenMemA kPtr acap ku' ⋆ (FullKittenFrame c s ⋆ R)) m_j) ?_ ?_
              · intro Js m_j ⟨ku', hnu', hinv', hsync', hlvl', hinc', hfail', hframe', hm'⟩
                c0_hsteps!
                exact ih_u (ui + 1#32, ku') m_j (by dsimp only; rw [hnu', hui1_nat]; omega)
                  ⟨by dsimp only; rw [hnu', hui1_nat]; exact hui_lt, hinv', hsync', hlvl', hinc',
                   hfail', hframe', hm'⟩
              · intro Js hJs
                c0_hsplit
                · have huv0 : ku.vals[ul.toNat]?.getD 0#32 = 0#32 := ‹_›
                  have hun0 := vals_some_zero_of_getD hinv_u hul_lt huv0
                  have hte_lt := trl_end_lt_nv_of_unassigned hinv_u hul_lt huv0
                  c0_hcall hAsg
                  · obtain ⟨_, hm_asg⟩ := kittenMemA_to_mem hm_u
                    exact ⟨acap, ku, FullKittenFrame c s ⋆ R, hinv_u.shapes, hacap_lt, hnv_u,
                      hul_lt, hte_lt, hm_asg, fun mA hmA => by
                        c0_hsteps!
                        have hucid_ne : ucid ≠ 0xFFFFFFFF#32 := by
                          intro h; have := congrArg BitVec.toNat h
                          change ucid.toNat = 2 ^ 32 - 1 at this; omega
                        have hent_ul : (cnfOfClauses (kittenOrigClauses ku)).EntailsClause
                            (cnfClause [ul.toNat]) := by simpa [hlits_u] using hwf_u.2.2.2.2.1
                        obtain ⟨hinv_a, hsync_a⟩ := kittenAssignStep_preserves_inv hinv_u hsync_u
                          hinc_u hul_lt hun0
                          (fun _ => ⟨hucid_ne, hent_ul, fun _ => ⟨hucid_ok.1, hlits_u⟩⟩)
                          (fun h => absurd h hucid_ne)
                          (Or.inr ⟨hucid_ok.1, by simp [hlits_u], fun x hx hxl => by
                            simp [hlits_u] at hx; exact absurd hx hxl⟩)
                        have hframe_a : SolveFrame ks0 (kittenAssignStep ku ul ucid) :=
                          SolveFrame.trans hframe_u ⟨rfl, rfl, rfl, rfl, rfl,
                            KittenCnfPermEquiv.refl _, fun _ _ => rfl, fun _ _ => rfl⟩
                        exact hJs _ ⟨kittenAssignStep ku ul ucid, rfl, hinv_a, hsync_a, hlvl_u,
                          hinc_u, hfail_u, hframe_a, kittenMem_to_amem hinv_a.shapes hmA⟩⟩
                · c0_hsteps!
                  exact hJs _ ⟨ku, rfl, hinv_u, hsync_u, hlvl_u, hinc_u, hfail_u, hframe_u, hm_u⟩
          · obtain ⟨_, hm_p0⟩ := kittenMemA_to_mem hm_u
            c0_hcall hProp
            · refine ⟨acap, ku, FullKittenFrame c s ⋆ R, hinv_u, hsync_u, hm_p0,
                fun confl_p ks_p m_p hinv_p hsync_p e_nv e_on e_lvl e_inc e_fail e_ant e_na e_ass
                  hperm hclAux hcore hdec hte_le htrl_kept hconfl_ff hconfl_ne hm_p => ?_⟩
              have hm_p' : (KittenMem kPtr ks_p ⋆ (FullKittenFrame c s ⋆ R)) m_p := hm_p
              clear hm_p
              c0_hsplit
              · have hc_fe : confl_p = 0xFFFFFFFE#32 := ‹_›
                c0_hsteps!
                have hframe_p : SolveFrame ks0 ks_p := SolveFrame.trans hframe_u
                  ⟨e_nv, e_on, e_ant, e_na, e_ass, hperm, hclAux, hcore⟩
                refine solve_m5_post_finish hlen h256 hscr_len hscr_ge rfl hinv_p (le_refl _)
                  hframe_p.nv hframe_p.orig_nc hframe_p.ante hframe_p.nassump hframe_p.assump
                  hframe_p.perm hframe_p.clAux (fun _ => hframe_p.core) (Or.inl rfl)
                  (fun h => absurd h (by decide)) ?_ hQ rfl
                rw [← hkPtr_eq]; exact sep_ac hm_p'
              · have hc_ne_fe : confl_p ≠ 0xFFFFFFFE#32 := ‹_›
                c0_hsplit
                · have hc_ne_ff : confl_p ≠ 0xFFFFFFFF#32 := ‹_›
                  have hmA_p : (KittenMemA kPtr acap ks_p ⋆ (FullKittenFrame c s ⋆ R)) m_p :=
                    kittenMem_to_amem hinv_p.shapes hm_p'
                  clear hm_p'
                  c0_hsteps!
                  obtain ⟨hc_lt, hc_fals⟩ := hconfl_ne hc_ne_ff hc_ne_fe
                  have ⟨hinv_i, _⟩ := inv_set_incons_lvl0 hinv_p hsync_p (e_lvl.trans hlvl_u)
                    hc_lt hc_fals
                  have huns_i := cnfOfClauses_unsat_append_left
                    (unitsCnf (kittenAssumpLits (ks_p.putHdr .incons confl_p)))
                    (hinv_i.clauses.incons_ok hc_ne_ff).2.1
                  have hframe_p : SolveFrame ks0 (ks_p.putHdr .incons confl_p) :=
                    SolveFrame.trans hframe_u ⟨e_nv, e_on, e_ant, e_na, e_ass, hperm, hclAux, hcore⟩
                  obtain ⟨_, hmFin_i⟩ := kittenMemA_to_mem hm
                  refine solve_m5_post_finish hlen h256 hscr_len hscr_ge rfl hinv_i (le_refl _)
                    hframe_p.nv hframe_p.orig_nc hframe_p.ante hframe_p.nassump hframe_p.assump
                    hframe_p.perm hframe_p.clAux (fun _ => hframe_p.core) (Or.inr (Or.inr rfl))
                    (fun _ => ⟨Or.inl hc_ne_ff, huns_i⟩) ?_ hQ rfl
                  rw [← hkPtr_eq]; exact sep_ac hmFin_i
                · have hc_ff : confl_p = 0xFFFFFFFF#32 := by
                    first | exact ‹_› | exact Classical.not_not.mp ‹_›
                  have hframe_p : SolveFrame ks0 ks_p := SolveFrame.trans hframe_u
                    ⟨e_nv, e_on, e_ant, e_na, e_ass, hperm, hclAux, hcore⟩
                  have hsi_p : SolveLoopInv acap ks0 ks_p 0xFFFFFFFF#32 :=
                    solveLoopInv_of_lvl0 hinv_p hsync_p (e_lvl.trans hlvl_u)
                      (e_inc.trans hinc_u) (e_fail.trans hfail_u) hframe_p
                  refine wp_while_state1
                    (fun st : BitVec 32 × KittenState × BitVec 64 => st.1)
                    (fun st => st.2.2.toNat)
                    (fun st m_l => st.2.2.toNat ≤ s.core.fuel.toNat ∧
                      SolveLoopInv acap ks0 st.2.1 st.1 ∧
                      (KittenMemA kPtr acap st.2.1 ⋆
                        (FullKittenFrame c { s with core := { s.core with fuel := st.2.2 } } ⋆
                          R)) m_l)
                    ?_ ?_
                  · intro Jm hJm; c0_hsteps!; rw [hc_ff]
                    exact hJm (0xFFFFFFFF#32, ks_p, s.core.fuel) m_p
                      ⟨le_refl _, hsi_p, kittenMem_to_amem hinv_p.shapes hm_p'⟩
                  · rintro Jm ⟨confl_m, km, fuel_m⟩ m_l ⟨hfuel_m, hsi_m, hm_l⟩ ih_m
                    dsimp only at hfuel_m hsi_m hm_l
                    c0_hsplit
                    · c0_hsplit
                      · have hfuel_pos : 0 < fuel_m.toNat := by bv_omega
                        have hfuel_sub : (fuel_m - 1#64).toNat = fuel_m.toNat - 1 := by bv_omega
                        let sFuel1 : FullState :=
                          { s with core := { s.core with fuel := fuel_m - 1#64 } }
                        have hfuel_le1 : (fuel_m - 1#64).toNat ≤ s.core.fuel.toNat := by omega
                        c0_hsplit
                        · have hconfl_ne : confl_m ≠ 0xFFFFFFFF#32 := ‹_›
                          have hm_l1 : (KittenMemA kPtr acap km ⋆
                              (FullKittenFrame c sFuel1 ⋆ R)) m := by
                            simpa only [sFuel1] using sep_ac hm
                          clear hm
                          c0_hsplit
                          · have hlvl0_m : km.lvl = 0#32 := ‹_›
                            c0_hsteps!
                            obtain ⟨hc_lt, hc_fals⟩ := hsi_m.confl_ok hconfl_ne
                            have ⟨hinv_i, _⟩ := inv_set_incons_lvl0 hsi_m.inv hsi_m.sync hlvl0_m
                              hc_lt hc_fals
                            have huns_i := cnfOfClauses_unsat_append_left
                              (unitsCnf (kittenAssumpLits (km.putHdr .incons confl_m)))
                              (hinv_i.clauses.incons_ok hconfl_ne).2.1
                            have hframe_i : SolveFrame ks0 (km.putHdr .incons confl_m) :=
                              SolveFrame.trans hsi_m.frame ⟨rfl, rfl, rfl, rfl, rfl,
                                KittenCnfPermEquiv.refl _, fun _ _ => rfl, fun _ _ => rfl⟩
                            obtain ⟨_, hmFin_i⟩ := kittenMemA_to_mem hm
                            refine solve_m5_post_finish hlen h256 hscr_len hscr_ge rfl hinv_i
                              hfuel_le1 hframe_i.nv hframe_i.orig_nc hframe_i.ante hframe_i.nassump
                              hframe_i.assump hframe_i.perm hframe_i.clAux (fun _ => hframe_i.core)
                              (Or.inr (Or.inr rfl)) (fun _ => ⟨Or.inl hconfl_ne, huns_i⟩) ?_ hQ rfl
                            rw [← hkPtr_eq]; exact sep_ac hmFin_i
                          · have hlvl_pos : 0 < km.lvl.toNat := by bv_omega
                            obtain ⟨hc_lt, hc_fals⟩ := hsi_m.confl_ok hconfl_ne
                            obtain ⟨iw, hiw, hiw_lvl⟩ := hsi_m.lvlne km.lvl.toNat hlvl_pos
                              (le_refl _)
                            have hiw_lvl_bv : km.lvlArr[(km.trl[iw]?.getD 0#32).toNat / 2]?.getD
                                0#32 = km.lvl := BitVec.eq_of_toNat_eq hiw_lvl
                            obtain ⟨_, hm_a0⟩ := kittenMemA_to_mem hm_l1
                            c0_hcall hAna
                            · refine ⟨acap, km, FullKittenFrame c sFuel1 ⋆ R, hsi_m.inv, hsi_m.sync,
                                hlvl_pos, ⟨iw, hiw, hiw_lvl_bv⟩, hc_lt, hc_fals, hm_a0,
                                fun ok_a ks_a m_a hinv_a e_nv e_on e_ant e_na e_ass e_inc e_fail
                                  horig_a hclAux_a hcore_a hok_a hm_a => ?_⟩
                              c0_hsplit
                              · have hok_t : ok_a = true := by cases ok_a <;> simp_all
                                obtain ⟨hsync_a, hlvl_lt, _, hdec_sub, hkept⟩ := hok_a hok_t
                                have hsi_a := solveLoopInv_of_analyze hsi_m.inv hsi_m.incons
                                  hsi_m.failing hsi_m.frame hsi_m.lvlne hsi_m.late hinv_a hsync_a
                                  e_nv e_on e_ant e_na e_ass e_inc e_fail horig_a hclAux_a hcore_a
                                  hlvl_lt hdec_sub hkept
                                c0_hcall hProp
                                · refine ⟨acap, ks_a, FullKittenFrame c sFuel1 ⋆ R, hsi_a.inv,
                                    hsi_a.sync, hm_a,
                                    fun confl_p2 ks_p2 m_p2 hinv_p2 hsync_p2 p_nv p_on p_lvl p_inc
                                      p_fail p_ant p_na p_ass p_perm p_clAux p_core p_te_le p_dec
                                      p_trl p_ff p_ne hm_p2 => ?_⟩
                                  c0_hsplit
                                  · have : confl_p2 = 0xFFFFFFFE#32 := ‹_›
                                    c0_hsteps!
                                    have hframe_p2 : SolveFrame ks0 ks_p2 :=
                                      SolveFrame.trans hsi_a.frame
                                        ⟨p_nv, p_on, p_ant, p_na, p_ass, p_perm, p_clAux, p_core⟩
                                    refine solve_m5_post_finish hlen h256 hscr_len hscr_ge rfl
                                      hinv_p2 hfuel_le1 hframe_p2.nv hframe_p2.orig_nc
                                      hframe_p2.ante hframe_p2.nassump hframe_p2.assump
                                      hframe_p2.perm hframe_p2.clAux (fun _ => hframe_p2.core)
                                      (Or.inl rfl) (fun h => absurd h (by decide)) ?_ hQ rfl
                                    rw [← hkPtr_eq]; exact sep_ac hm_p2
                                  · have hc_ne2 : confl_p2 ≠ 0xFFFFFFFE#32 := ‹_›
                                    have hsi_p2 := solveLoopInv_of_propagate hsi_a.inv hsi_a.incons
                                      hsi_a.failing hsi_a.frame hsi_a.lvlne hsi_a.late hinv_p2
                                      hsync_p2 p_nv p_on p_lvl p_inc p_fail p_ant p_na p_ass p_perm
                                      p_clAux p_core p_dec p_te_le p_trl hc_ne2 (p_ne · hc_ne2)
                                    c0_hsteps!
                                    exact ih_m (confl_p2, ks_p2, fuel_m - 1#64) _
                                      (by dsimp only; omega)
                                      ⟨hfuel_le1, hsi_p2, kittenMem_to_amem hinv_p2.shapes hm_p2⟩
                              · c0_hsteps!
                                have hperm_a : KittenCnfPermEquiv (kittenOrigClauses ks_a)
                                    (kittenOrigClauses km) := by
                                  rw [horig_a]; exact KittenCnfPermEquiv.refl _
                                have hframe_a : SolveFrame ks0 ks_a := SolveFrame.trans hsi_m.frame
                                  ⟨e_nv, e_on, e_ant, e_na, e_ass, hperm_a, hclAux_a, hcore_a⟩
                                refine solve_m5_post_finish hlen h256 hscr_len hscr_ge rfl hinv_a
                                  hfuel_le1 hframe_a.nv hframe_a.orig_nc hframe_a.ante
                                  hframe_a.nassump hframe_a.assump hframe_a.perm hframe_a.clAux
                                  (fun _ => hframe_a.core) (Or.inl rfl)
                                  (fun h => absurd h (by decide)) ?_ hQ rfl
                                rw [← hkPtr_eq]; exact sep_ac hm_a
                        · have hconfl_ff : confl_m = 0xFFFFFFFF#32 := by
                            first | exact ‹_› | exact Classical.not_not.mp ‹_›
                          have hm_l1 : (KittenMemA kPtr acap km ⋆
                              (FullKittenFrame c sFuel1 ⋆ R)) m := by
                            simpa only [sFuel1] using sep_ac hm
                          clear hm
                          c0_hsteps_nogrp
                          refine wp_while_break_state
                            (β := BitVec 32 × BitVec 32 × Bool × KittenState)
                            (fun bst => ((bst.1, bst.2.1, bst.2.2.1, ()) :
                              Tup Val [i32, i32, .bool]))
                            (fun bst m_b =>
                              (bst.2.2.1 = false → bst.1 = 0xFFFFFFFF#32 ∧ bst.2.2.2 = km ∧
                                ∀ j < km.nassump.toNat,
                                  km.vals[(km.assump[j]?.getD 0#32).toNat]? = some 1#32) ∧
                              (bst.2.2.1 = true →
                                bst.2.2.2.Inv acap ∧ SolveFrame ks0 bst.2.2.2 ∧
                                (bst.1 ≠ 0xFFFFFFFE#32 →
                                  SolveLoopInv acap ks0 bst.2.2.2 bst.1)) ∧
                              (KittenMemA kPtr acap bst.2.2.2 ⋆
                                (FullKittenFrame c sFuel1 ⋆ R)) m_b)
                            (α := BitVec 32)
                            (fun st => ((st, ()) : Tup Val [i32]))
                            (fun st => km.nassump.toNat - st.toNat)
                            (fun st m_b =>
                              st.toNat ≤ km.nassump.toNat ∧
                              (∀ j < st.toNat,
                                km.vals[(km.assump[j]?.getD 0#32).toNat]? = some 1#32) ∧
                              (KittenMemA kPtr acap km ⋆ (FullKittenFrame c sFuel1 ⋆ R)) m_b)
                            ?_ ?_ ?_
                          · rintro B ⟨confl_b, ad_b, did_b, ks_b⟩ m_b ⟨hf_b, ht_b, hm_b⟩
                            dsimp only at hf_b ht_b hm_b
                            c0_hsplit
                            · have hfe_b : confl_b = 0xFFFFFFFE#32 := ‹_›
                              c0_hsteps!
                              have hdid_t : did_b = true := by
                                cases did_b
                                · obtain ⟨hc, _⟩ := hf_b rfl; rw [hc] at hfe_b; cases hfe_b
                                · rfl
                              obtain ⟨hinv_b, hframe_b, _⟩ := ht_b hdid_t
                              obtain ⟨_, hmFin_b⟩ := kittenMemA_to_mem hm_b
                              refine solve_m5_post_finish hlen h256 hscr_len hscr_ge rfl hinv_b
                                hfuel_le1 hframe_b.nv hframe_b.orig_nc hframe_b.ante
                                hframe_b.nassump hframe_b.assump hframe_b.perm hframe_b.clAux
                                (fun _ => hframe_b.core) (Or.inl rfl)
                                (fun h => absurd h (by decide)) ?_ hQ rfl
                              rw [← hkPtr_eq]; exact sep_ac hmFin_b
                            · have hne_fe_b : confl_b ≠ 0xFFFFFFFE#32 := ‹_›
                              c0_hsplit
                              · have hdid_t : did_b = true := ‹_›
                                c0_hsteps!
                                obtain ⟨_, _, hsi_b⟩ := ht_b hdid_t
                                exact ih_m (confl_b, ks_b, fuel_m - 1#64) _ (by dsimp only; omega)
                                  ⟨hfuel_le1, hsi_b hne_fe_b, hm_b⟩
                              · have hdid_f : did_b = false := by cases did_b <;> simp_all
                                obtain ⟨_, hks_b_eq, hall_ass_j⟩ := hf_b hdid_f
                                subst ks_b
                                have hall_ass_mem : ∀ a ∈ kittenAssumpLits km,
                                    km.vals[a]? = some 1#32 := by
                                  intro a ha
                                  simp only [kittenAssumpLits, List.mem_map,
                                    List.mem_take_iff_getElem] at ha
                                  obtain ⟨ab, ⟨ia, hia, rfl⟩, rfl⟩ := ha
                                  have hlen_a : km.nassump.toNat ≤ km.assump.length := by
                                    rw [hsi_m.inv.shapes.assump_len]
                                    exact hsi_m.inv.clauses.nassump_le
                                  have hget := hall_ass_j ia (by omega)
                                  rwa [List.getElem?_eq_getElem (by omega : ia < km.assump.length),
                                    Option.getD_some] at hget
                                c0_hsplit
                                · c0_hsteps!
                                  obtain ⟨_, hmFin_b⟩ := kittenMemA_to_mem hm_b
                                  refine solve_m5_post_finish hlen h256 hscr_len hscr_ge rfl
                                    hsi_m.inv hfuel_le1 hsi_m.frame.nv hsi_m.frame.orig_nc
                                    hsi_m.frame.ante hsi_m.frame.nassump hsi_m.frame.assump
                                    hsi_m.frame.perm hsi_m.frame.clAux (fun _ => hsi_m.frame.core)
                                    (Or.inr (Or.inl rfl)) (fun h => absurd h (by decide)) ?_ hQ rfl
                                  rw [← hkPtr_eq]; exact sep_ac hmFin_b
                                · have hnv_m := hsi_m.inv.clauses.nv_le
                                  c0_hsteps_nogrp
                                  refine wp_while_break_state
                                    (β := BitVec 32 × BitVec 32 × BitVec 32)
                                    (fun bst => (bst.1, bst.2.1, bst.2.2, ()))
                                    (fun bst m_v =>
                                      (bst.2.1 = 0xFFFFFFFF#32 ∨
                                        (bst.2.1.toNat < km.nv.toNat ∧
                                          km.vals[2 * bst.2.1.toNat]?.getD 0#32 = 0#32)) ∧
                                      (KittenMemA kPtr acap km ⋆
                                        (FullKittenFrame c sFuel1 ⋆ R)) m_v)
                                    (α := BitVec 32 × BitVec 32)
                                    (fun st => (st.1, st.2, ()))
                                    (fun st => km.nv.toNat - st.2.toNat)
                                    (fun st m_v =>
                                      st.2.toNat ≤ km.nv.toNat ∧
                                      (KittenMemA kPtr acap km ⋆
                                        (FullKittenFrame c sFuel1 ⋆ R)) m_v)
                                    ?_ ?_ ?_
                                  · rintro B1 ⟨_c1, pick1, _s1⟩ m_v1 ⟨hpick1, hm_v1⟩
                                    dsimp only at hpick1 hm_v1
                                    refine wp_join_state
                                      (proj := fun p : BitVec 32 × BitVec 32 × BitVec 32 =>
                                        (p.1, p.2.1, p.2.2, ()))
                                      (fun p m_v2 =>
                                        (p.2.1 = 0xFFFFFFFF#32 ∨
                                          (p.2.1.toNat < km.nv.toNat ∧
                                            km.vals[2 * p.2.1.toNat]?.getD 0#32 = 0#32)) ∧
                                        (KittenMemA kPtr acap km ⋆
                                          (FullKittenFrame c sFuel1 ⋆ R)) m_v2)
                                      ?_ ?_
                                    · intro J2 ⟨_c2, pick2, _s2⟩ m_v2 ⟨hpick2, hm_v2⟩
                                      dsimp only at hpick2 hm_v2
                                      refine wp_join_state
                                        (proj := fun p : BitVec 32 × BitVec 32 => (p.1, p.2, ()))
                                        (fun p m_v3 =>
                                          (p.2 = 0xFFFFFFFF#32 ∨
                                            (p.2.toNat < km.nv.toNat ∧
                                              km.vals[2 * p.2.toNat]?.getD 0#32 = 0#32)) ∧
                                          (KittenMemA kPtr acap km ⋆
                                            (FullKittenFrame c sFuel1 ⋆ R)) m_v3)
                                        ?_ ?_
                                      · intro J3 ⟨_c3, pick3⟩ m_v3 ⟨hpick3, hm_v3⟩
                                        dsimp only at hpick3 hm_v3
                                        c0_hsplit
                                        · c0_hsteps!
                                          obtain ⟨_, hmFin_v⟩ := kittenMemA_to_mem hm_v3
                                          refine solve_m5_post_finish hlen h256 hscr_len hscr_ge rfl
                                            hsi_m.inv hfuel_le1 hsi_m.frame.nv hsi_m.frame.orig_nc
                                            hsi_m.frame.ante hsi_m.frame.nassump hsi_m.frame.assump
                                            hsi_m.frame.perm hsi_m.frame.clAux
                                            (fun _ => hsi_m.frame.core) (Or.inr (Or.inl rfl))
                                            (fun h => absurd h (by decide)) ?_ hQ rfl
                                          rw [← hkPtr_eq]; exact sep_ac hmFin_v
                                        · have hpk_ne : pick3 ≠ 0xFFFFFFFF#32 := ‹_›
                                          rcases hpick3 with rfl | ⟨hpk_lt, hpk_val⟩
                                          · exact absurd rfl hpk_ne
                                          have hpk_wrap : pick3.toNat < 2 ^ 28 := by
                                            unfold kMaxV at hnv_m; omega
                                          have hpk_128 : pick3.toNat < 128 := by
                                            unfold kMaxV at hnv_m; omega
                                          let ks_q := km.putHdr .qsearch pick3
                                          have hinv_q := inv_set_qsearch hsi_m.inv pick3
                                          have hsync_q : KittenTrailSynced ks_q := hsi_m.sync
                                          have hframe_q : SolveFrame ks0 ks_q :=
                                            SolveFrame.trans hsi_m.frame
                                              ⟨rfl, rfl, rfl, rfl, rfl, KittenCnfPermEquiv.refl _,
                                               fun _ _ => rfl, fun _ _ => rfl⟩
                                          let ph : BitVec 32 :=
                                            (ks_q.flags[pick3.toNat]?.getD 0#32 ^^^ ks_q.phase) &&&
                                              1#32
                                          have hq_nv : ks_q.nv = km.nv := rfl
                                          have hq_lvl : ks_q.lvl = km.lvl := rfl
                                          have hph_lt : ph.toNat < 2 := by
                                            dsimp only [ph]; rw [BitVec.toNat_and]
                                            have h1 : (1#32 : BitVec 32).toNat = 1 := rfl
                                            rw [h1]
                                            exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
                                          let lit_d := (pick3 <<< (1 : Nat)) ||| ph
                                          have hlit_d := bv32_shl1_or_bit_m5 hpk_lt hnv_m hph_lt
                                          have hlit_0 : ks_q.vals[lit_d.toNat]? = some 0#32 := by
                                            have hz0 := vals_some_zero_of_getD hinv_q
                                              (show 2 * pick3.toNat < 2 * ks_q.nv.toNat by
                                                rw [hq_nv]; omega) hpk_val
                                            rcases (by omega : ph.toNat = 0 ∨ ph.toNat = 1) with
                                              h0 | h1
                                            · rwa [hlit_d.1, h0, Nat.add_zero]
                                            · have hxor : 2 * pick3.toNat + 1 =
                                                  (2 * pick3.toNat) ^^^ 1 := by
                                                rcases nat_xor1_cases (2 * pick3.toNat) with
                                                  ⟨_, _⟩ | ⟨_, _⟩ <;> omega
                                              rw [hlit_d.1, h1, hxor]
                                              exact vals_pair_some_zero hinv_q
                                                (by rw [hq_nv]; omega) hz0
                                          have hle_te := lvl_le_trl_end hinv_q hsi_m.lvlne
                                          have hte_le := hinv_q.assign.trl_end_le
                                          have hlvl_wrap : ks_q.lvl.toNat + 1 < 2 ^ 32 := by
                                            dsimp only [ks_q]
                                            rw [hq_nv] at hte_le; unfold kMaxV at hnv_m; omega
                                          let ks_l := ks_q.putHdr .lvl (ks_q.lvl + 1#32)
                                          have hte_lt := trl_end_lt_nv_of_unassigned hinv_q
                                            (by rw [hq_nv]; exact hlit_d.2) (by rw [hlit_0]; rfl)
                                          c0_hsteps_nogrp
                                          c0_hcall hAsg
                                          · obtain ⟨_, hm_asg⟩ := kittenMemA_to_mem hm
                                            exact ⟨acap, ks_l, FullKittenFrame c sFuel1 ⋆ R,
                                              hinv_q.shapes.putHdr .lvl _, hacap_lt, hnv_m,
                                              hlit_d.2, hte_lt, hm_asg, fun mA hmA => by
                                                obtain ⟨hinv_d, hsync_d, hinc_d, hframe_d,
                                                  hlvlne_d, hlate_d⟩ :=
                                                  decide_step_preserves hinv_q hsync_q hsi_m.incons
                                                    hframe_q hsi_m.lvlne hsi_m.late hlit_d.2 hlit_0
                                                    (fun _ a ha => hall_ass_mem a ha)
                                                c0_hcall hProp
                                                · refine ⟨acap, kittenAssignStep ks_l lit_d
                                                    0xFFFFFFFF#32, FullKittenFrame c sFuel1 ⋆ R,
                                                    hinv_d, hsync_d, hmA,
                                                    fun confl_p2 ks_p2 m_p2 hinv_p2 hsync_p2 p_nv
                                                      p_on p_lvl p_inc p_fail p_ant p_na p_ass
                                                      p_perm p_clAux p_core p_te_le p_dec p_trl
                                                      _ p_ne hm_p2 => ?_⟩
                                                  c0_hsplit
                                                  · have : confl_p2 = 0xFFFFFFFE#32 := ‹_›
                                                    c0_hsteps!
                                                    have hframe_p2 : SolveFrame ks0 ks_p2 :=
                                                      SolveFrame.trans hframe_d
                                                        ⟨p_nv, p_on, p_ant, p_na, p_ass, p_perm,
                                                         p_clAux, p_core⟩
                                                    refine solve_m5_post_finish hlen h256 hscr_len
                                                      hscr_ge rfl hinv_p2 hfuel_le1 hframe_p2.nv
                                                      hframe_p2.orig_nc hframe_p2.ante
                                                      hframe_p2.nassump hframe_p2.assump
                                                      hframe_p2.perm hframe_p2.clAux
                                                      (fun _ => hframe_p2.core) (Or.inl rfl)
                                                      (fun h => absurd h (by decide)) ?_ hQ rfl
                                                    rw [← hkPtr_eq]; exact sep_ac hm_p2
                                                  · have hc_ne2 : confl_p2 ≠ 0xFFFFFFFE#32 := ‹_›
                                                    have hsi_p2 := solveLoopInv_of_propagate hinv_d
                                                      hinc_d hsi_m.failing hframe_d hlvlne_d hlate_d
                                                      hinv_p2 hsync_p2 p_nv p_on p_lvl p_inc p_fail
                                                      p_ant p_na p_ass p_perm p_clAux p_core p_dec
                                                      p_te_le p_trl hc_ne2 (p_ne · hc_ne2)
                                                    c0_hsteps!
                                                    exact ih_m (confl_p2, ks_p2, fuel_m - 1#64) _
                                                      (by dsimp only; omega)
                                                      ⟨hfuel_le1, hsi_p2,
                                                       kittenMem_to_amem hinv_p2.shapes hm_p2⟩⟩
                                      · intro J3 hJ3
                                        c0_hsplit
                                        · have hpk2_ff : pick2 = 0xFFFFFFFF#32 := ‹_›
                                          subst pick2
                                          refine wp_while_break_state
                                            (β := BitVec 32 × BitVec 32)
                                            (fun bst => ((bst.1, bst.2, ()) : Tup Val [i32, i32]))
                                            (fun bst m_v3 =>
                                              (bst.2 = 0xFFFFFFFF#32 ∨
                                                (bst.2.toNat < km.nv.toNat ∧
                                                  km.vals[2 * bst.2.toNat]?.getD 0#32 = 0#32)) ∧
                                              (KittenMemA kPtr acap km ⋆
                                                (FullKittenFrame c sFuel1 ⋆ R)) m_v3)
                                            (α := BitVec 32)
                                            (fun st => ((st, ()) : Tup Val [i32]))
                                            (fun st => km.nv.toNat - st.toNat)
                                            (fun st m_v3 =>
                                              st.toNat ≤ km.nv.toNat ∧
                                              (KittenMemA kPtr acap km ⋆
                                                (FullKittenFrame c sFuel1 ⋆ R)) m_v3)
                                            ?_ ?_ ?_
                                          · rintro B3 ⟨c3, pk3⟩ m_v3 ⟨hpk3, hm_v3⟩
                                            exact hJ3 (c3, pk3) m_v3 ⟨hpk3, hm_v3⟩
                                          · rintro B3 L3 c3 m_v3 hB3 hL3 ⟨hc3_le, hm_v3⟩
                                            c0_hsplit
                                            · have hc3_lt : c3.toNat < km.nv.toNat := by bv_omega
                                              have hc3_2 : 2 * c3.toNat < 256 := by
                                                unfold kMaxV at hnv_m; omega
                                              have hc3_2w : 2 * c3.toNat < 2 ^ 28 := by omega
                                              have hc3_shl : (c3 <<< (1 : Nat)).toNat =
                                                  2 * c3.toNat := by
                                                rw [BitVec.toNat_shiftLeft]; simp; omega
                                              have hc3_shl_w : (c3 <<< (1 : Nat)).toNat < 2 ^ 28 :=
                                                by rw [hc3_shl]; exact hc3_2w
                                              have hc3_shl_256 : (c3 <<< (1 : Nat)).toNat < 256 :=
                                                by rw [hc3_shl]; exact hc3_2
                                              have hc3_1 : (c3 + 1#32).toNat = c3.toNat + 1 := by
                                                unfold kMaxV at hnv_m; bv_omega
                                              c0_hsplit
                                              · have hval0 : km.vals[2 * c3.toNat]?.getD 0#32 =
                                                    0#32 := by rwa [← hc3_shl]
                                                c0_hsteps!
                                                exact hB3 (c3, c3) m_v3
                                                  ⟨Or.inr ⟨hc3_lt, hval0⟩, hm_v3⟩
                                              · c0_hsteps!
                                                exact hL3 (c3 + 1#32) m_v3
                                                  (by rw [hc3_1]; omega)
                                                  ⟨by rw [hc3_1]; omega, hm_v3⟩
                                            · exact hB3 (c3, 0xFFFFFFFF#32) m_v3 ⟨Or.inl rfl, hm_v3⟩
                                          · intro B3 L3 hB3 hL3
                                            exact wp_jump_state
                                              (proj := fun st : BitVec 32 => (st, ()))
                                              0#32 rfl (hL3 _ _ ⟨by simp, hm_v2⟩)
                                        · exact wp_jump_state
                                            (proj := fun p : BitVec 32 × BitVec 32 =>
                                              (p.1, p.2, ()))
                                            (_c2, pick2) rfl (hJ3 (_c2, pick2) m_v2 ⟨hpick2, hm_v2⟩)
                                    · intro J2 hJ2
                                      c0_hsplit
                                      · have hpk1_ff : pick1 = 0xFFFFFFFF#32 := ‹_›
                                        subst pick1
                                        c0_hsteps_nogrp
                                        refine wp_while_break_state
                                          (β := BitVec 32 × BitVec 32 × BitVec 32)
                                          (fun bst => (bst.1, bst.2.1, bst.2.2, ()))
                                          (fun bst m_v2 =>
                                            (bst.2.1 = 0xFFFFFFFF#32 ∨
                                              (bst.2.1.toNat < km.nv.toNat ∧
                                                km.vals[2 * bst.2.1.toNat]?.getD 0#32 = 0#32)) ∧
                                            (KittenMemA kPtr acap km ⋆
                                              (FullKittenFrame c sFuel1 ⋆ R)) m_v2)
                                          (α := BitVec 32 × BitVec 32)
                                          (fun st => (st.1, st.2, ()))
                                          (fun st => km.nv.toNat - st.2.toNat)
                                          (fun st m_v2 =>
                                            st.2.toNat ≤ km.nv.toNat ∧
                                            (KittenMemA kPtr acap km ⋆
                                              (FullKittenFrame c sFuel1 ⋆ R)) m_v2)
                                          ?_ ?_ ?_
                                        · rintro B2 ⟨c2, pk2, s2⟩ m_v2 ⟨hpk2, hm_v2⟩
                                          exact hJ2 (c2, pk2, s2) m_v2 ⟨hpk2, hm_v2⟩
                                        · rintro B2 L2 ⟨c2, s2⟩ m_v2 hB2 hL2 ⟨hs2_le, hm_v2⟩
                                          c0_hsplit
                                          · c0_hsplit
                                            · have hc2_lt : c2.toNat < km.nv.toNat := by bv_omega
                                              have hs2_lt : s2.toNat < km.nv.toNat := by bv_omega
                                              have hc2_128 : c2.toNat < 128 := by
                                                unfold kMaxV at hnv_m; omega
                                              have hc2_w : c2.toNat < 2 ^ 28 := by omega
                                              have hc2_2 : 2 * c2.toNat < 256 := by
                                                unfold kMaxV at hnv_m; omega
                                              have hc2_2w : 2 * c2.toNat < 2 ^ 28 := by omega
                                              have hc2_shl : (c2 <<< (1 : Nat)).toNat =
                                                  2 * c2.toNat := by
                                                rw [BitVec.toNat_shiftLeft]; simp; omega
                                              have hc2_shl_w : (c2 <<< (1 : Nat)).toNat < 2 ^ 28 :=
                                                by rw [hc2_shl]; exact hc2_2w
                                              have hc2_shl_256 : (c2 <<< (1 : Nat)).toNat < 256 :=
                                                by rw [hc2_shl]; exact hc2_2
                                              have hs2_1 : (s2 + 1#32).toNat = s2.toNat + 1 := by
                                                unfold kMaxV at hnv_m; bv_omega
                                              c0_hsplit
                                              · have hval0 : km.vals[2 * c2.toNat]?.getD 0#32 =
                                                    0#32 := by rwa [← hc2_shl]
                                                c0_hsteps!
                                                exact hB2 (c2, c2, s2) m_v2
                                                  ⟨Or.inr ⟨hc2_lt, hval0⟩, hm_v2⟩
                                              · c0_hsteps!
                                                exact hL2 (km.qprev[c2.toNat]?.getD 0#32, s2 + 1#32)
                                                  m_v2 (by dsimp only; rw [hs2_1]; omega)
                                                  ⟨by dsimp only; rw [hs2_1]; omega, hm_v2⟩
                                            · exact hB2 (c2, 0xFFFFFFFF#32, s2) m_v2
                                                ⟨Or.inl rfl, hm_v2⟩
                                          · exact hB2 (c2, 0xFFFFFFFF#32, s2) m_v2
                                              ⟨Or.inl rfl, hm_v2⟩
                                        · intro B2 L2 hB2 hL2
                                          exact wp_jump_state
                                            (proj := fun st : BitVec 32 × BitVec 32 =>
                                              (st.1, st.2, ()))
                                            (km.qlast, 0#32) rfl (hL2 _ _ ⟨by simp, hm_v1⟩)
                                      · exact wp_jump_state
                                          (proj := fun p : BitVec 32 × BitVec 32 × BitVec 32 =>
                                            (p.1, p.2.1, p.2.2, ()))
                                          (_c1, pick1, _s1) rfl
                                          (hJ2 (_c1, pick1, _s1) m_v1 ⟨hpick1, hm_v1⟩)
                                  · rintro B1 L1 ⟨c1, s1⟩ m_v1 hB1 hL1 ⟨hs1_le, hm_v1⟩
                                    c0_hsplit
                                    · c0_hsplit
                                      · have hc1_lt : c1.toNat < km.nv.toNat := by bv_omega
                                        have hs1_lt : s1.toNat < km.nv.toNat := by bv_omega
                                        have hc1_128 : c1.toNat < 128 := by
                                          unfold kMaxV at hnv_m; omega
                                        have hc1_w : c1.toNat < 2 ^ 28 := by omega
                                        have hc1_2 : 2 * c1.toNat < 256 := by
                                          unfold kMaxV at hnv_m; omega
                                        have hc1_2w : 2 * c1.toNat < 2 ^ 28 := by omega
                                        have hc1_shl : (c1 <<< (1 : Nat)).toNat = 2 * c1.toNat := by
                                          rw [BitVec.toNat_shiftLeft]; simp; omega
                                        have hc1_shl_w : (c1 <<< (1 : Nat)).toNat < 2 ^ 28 := by
                                          rw [hc1_shl]; exact hc1_2w
                                        have hc1_shl_256 : (c1 <<< (1 : Nat)).toNat < 256 := by
                                          rw [hc1_shl]; exact hc1_2
                                        have hs1_1 : (s1 + 1#32).toNat = s1.toNat + 1 := by
                                          unfold kMaxV at hnv_m; bv_omega
                                        c0_hsplit
                                        · have hval0 : km.vals[2 * c1.toNat]?.getD 0#32 = 0#32 := by
                                            rwa [← hc1_shl]
                                          c0_hsteps!
                                          exact hB1 (c1, c1, s1) m_v1
                                            ⟨Or.inr ⟨hc1_lt, hval0⟩, hm_v1⟩
                                        · c0_hsteps!
                                          exact hL1 (km.qprev[c1.toNat]?.getD 0#32, s1 + 1#32)
                                            m_v1 (by dsimp only; rw [hs1_1]; omega)
                                            ⟨by dsimp only; rw [hs1_1]; omega, hm_v1⟩
                                      · exact hB1 (c1, 0xFFFFFFFF#32, s1) m_v1 ⟨Or.inl rfl, hm_v1⟩
                                    · exact hB1 (c1, 0xFFFFFFFF#32, s1) m_v1 ⟨Or.inl rfl, hm_v1⟩
                                  · intro B1 L1 hB1 hL1
                                    exact wp_jump_state
                                      (proj := fun st : BitVec 32 × BitVec 32 => (st.1, st.2, ()))
                                      (km.qsearch, 0#32) rfl (hL1 _ _ ⟨by simp, hm_b⟩)
                          · rintro B0 L0 ad_a m_a hB0 hL0 ⟨had_le, hall_j, hm_a⟩
                            c0_hsplit
                            · have had_lt : ad_a.toNat < km.nassump.toNat := by bv_omega
                              have hna_le := hsi_m.inv.clauses.nassump_le
                              have hnv_m := hsi_m.inv.clauses.nv_le
                              have had_128 : ad_a.toNat < 128 := by unfold kMaxV at hna_le; omega
                              have had_w : ad_a.toNat < 2 ^ 28 := by omega
                              have had_1 : (ad_a + 1#32).toNat = ad_a.toNat + 1 := by
                                unfold kMaxV at hna_le; bv_omega
                              let alit := km.assump[ad_a.toNat]?.getD 0#32
                              have halit_lt : alit.toNat < 2 * km.nv.toNat :=
                                hsi_m.inv.clauses.assump_ok ad_a.toNat had_lt
                              have halit_256 : alit.toNat < 256 := by unfold kMaxV at hnv_m; omega
                              have halit_w : alit.toNat < 2 ^ 28 := by omega
                              have hlen_a : km.nassump.toNat ≤ km.assump.length := by
                                rw [hsi_m.inv.shapes.assump_len]; exact hna_le
                              have halit_mem : alit.toNat ∈ kittenAssumpLits km :=
                                mem_kittenAssumpLits_of_lt_m5 hlen_a had_lt
                              c0_hsplit
                              · have hav2 : km.vals[alit.toNat]?.getD 0#32 = 2#32 := ‹_›
                                have hav2' : km.vals[alit.toNat]? = some 2#32 := by
                                  have hl : alit.toNat < km.vals.length := by
                                    rw [hsi_m.inv.shapes.vals_len]; exact halit_256
                                  rw [List.getElem?_eq_getElem hl, Option.getD_some] at hav2
                                  rw [List.getElem?_eq_getElem hl, hav2]
                                obtain ⟨hdec_in, huns_bf⟩ := allDecisionsInAssumps_of_late
                                  hsi_m.inv hsi_m.sync hsi_m.late halit_mem hav2'
                                obtain ⟨_, hm_bf0⟩ := kittenMemA_to_mem hm_a
                                c0_hcall hBf
                                · refine ⟨acap, km, FullKittenFrame c sFuel1 ⋆ R, hsi_m.inv,
                                    hsi_m.sync, halit_lt, halit_mem, hav2', hdec_in, hm_bf0,
                                    fun ks_bf m_bf hinv_bf _ hfail_bf hpres_bf hm_bf => ?_⟩
                                  c0_hsteps!
                                  have huns_bf' : (cnfOfClauses (kittenOrigClauses ks_bf) ++
                                      unitsCnf (kittenAssumpLits ks_bf)).Unsat := by
                                    unfold kittenAssumpLits
                                    rw [hpres_bf.orig_eq, hpres_bf.nassump, hpres_bf.assump]
                                    exact huns_bf
                                  refine solve_m5_post_finish hlen h256 hscr_len hscr_ge rfl hinv_bf
                                    hfuel_le1 (hpres_bf.nv.trans hsi_m.frame.nv)
                                    (hpres_bf.orig_nc.trans hsi_m.frame.orig_nc)
                                    (hpres_bf.ante.trans hsi_m.frame.ante)
                                    (hpres_bf.nassump.trans hsi_m.frame.nassump)
                                    (hpres_bf.assump.trans hsi_m.frame.assump) ?_ ?_
                                    (fun h => absurd rfl h) (Or.inr (Or.inr rfl))
                                    (fun _ => ⟨Or.inr (by rw [hfail_bf]; decide), huns_bf'⟩)
                                    ?_ hQ rfl
                                  · rw [hpres_bf.orig_eq]; exact hsi_m.frame.perm
                                  · intro ci hci
                                    rw [hpres_bf.clAux_eq ci
                                      (by rw [hsi_m.frame.orig_nc]; exact hci)]
                                    exact hsi_m.frame.clAux ci hci
                                  · rw [← hkPtr_eq]; exact sep_ac hm_bf
                              · c0_hsplit
                                · have hav0 : km.vals[alit.toNat]?.getD 0#32 = 0#32 := ‹_›
                                  have halit_0 := vals_some_zero_of_getD hsi_m.inv halit_lt hav0
                                  have hle_te := lvl_le_trl_end hsi_m.inv hsi_m.lvlne
                                  have hte_le := hsi_m.inv.assign.trl_end_le
                                  have hlvl_wrap : km.lvl.toNat + 1 < 2 ^ 32 := by
                                    unfold kMaxV at hnv_m; omega
                                  let km_l := km.putHdr .lvl (km.lvl + 1#32)
                                  have hte_lt := trl_end_lt_nv_of_unassigned hsi_m.inv halit_lt hav0
                                  c0_hsteps_nogrp
                                  c0_hcall hAsg
                                  · obtain ⟨_, hm_asg⟩ := kittenMemA_to_mem hm
                                    exact ⟨acap, km_l, FullKittenFrame c sFuel1 ⋆ R,
                                      hsi_m.inv.shapes.putHdr .lvl _, hacap_lt, hnv_m, halit_lt,
                                      hte_lt, hm_asg, fun mA hmA => by
                                        obtain ⟨hinv_d, hsync_d, hinc_d, hframe_d, hlvlne_d,
                                          hlate_d⟩ :=
                                          decide_step_preserves hsi_m.inv hsi_m.sync hsi_m.incons
                                            hsi_m.frame hsi_m.lvlne hsi_m.late halit_lt halit_0
                                            (fun hnot => absurd halit_mem hnot)
                                        c0_hcall hProp
                                        · refine ⟨acap, kittenAssignStep km_l alit 0xFFFFFFFF#32,
                                            FullKittenFrame c sFuel1 ⋆ R, hinv_d, hsync_d, hmA,
                                            fun confl_p2 ks_p2 m_p2 hinv_p2 hsync_p2 p_nv p_on
                                              p_lvl p_inc p_fail p_ant p_na p_ass p_perm p_clAux
                                              p_core p_te_le p_dec p_trl _ p_ne hm_p2 => ?_⟩
                                          c0_hsteps!
                                          have hframe_p2 : SolveFrame ks0 ks_p2 :=
                                            SolveFrame.trans hframe_d
                                              ⟨p_nv, p_on, p_ant, p_na, p_ass, p_perm, p_clAux,
                                               p_core⟩
                                          exact hB0 (confl_p2, ad_a, true, ks_p2) m_p2
                                            ⟨(fun h => by dsimp only at h; cases h), fun _ =>
                                              ⟨hinv_p2, hframe_p2, fun hc_ne =>
                                                solveLoopInv_of_propagate hinv_d hinc_d
                                                  hsi_m.failing hframe_d hlvlne_d hlate_d hinv_p2
                                                  hsync_p2 p_nv p_on p_lvl p_inc p_fail p_ant p_na
                                                  p_ass p_perm p_clAux p_core p_dec p_te_le p_trl
                                                  hc_ne (p_ne · hc_ne)⟩,
                                             kittenMem_to_amem hinv_p2.shapes hm_p2⟩⟩
                                · have hne2 : km.vals[alit.toNat]?.getD 0#32 ≠ 2#32 := ‹_›
                                  have hne0 : km.vals[alit.toNat]?.getD 0#32 ≠ 0#32 := ‹_›
                                  have hav1 : km.vals[alit.toNat]?.getD 0#32 = 1#32 := by
                                    rcases hsi_m.inv.assign.vals_dom alit.toNat halit_lt with
                                      h0 | h1 | h2
                                    · exact absurd h0 hne0
                                    · exact h1
                                    · exact absurd h2 hne2
                                  have hav1' : km.vals[alit.toNat]? = some 1#32 := by
                                    have hl : alit.toNat < km.vals.length := by
                                      rw [hsi_m.inv.shapes.vals_len]; exact halit_256
                                    rw [List.getElem?_eq_getElem hl, Option.getD_some] at hav1
                                    rw [List.getElem?_eq_getElem hl, hav1]
                                  c0_hsteps!
                                  refine hL0 (ad_a + 1#32) m_a (by rw [had_1]; omega)
                                    ⟨by rw [had_1]; exact had_lt,
                                     fun j hj => by
                                       rw [had_1] at hj
                                       by_cases hja : j = ad_a.toNat
                                       · subst hja; exact hav1'
                                       · exact hall_j j (by omega),
                                     hm_a⟩
                            · exact hB0 (confl_m, ad_a, false, km) m_a
                                ⟨fun _ => ⟨hconfl_ff, rfl, fun j hj => by
                                  have heq : ad_a.toNat = km.nassump.toNat := by bv_omega
                                  rw [← heq] at hj; exact hall_j j hj⟩,
                                 (fun h => by dsimp only at h; cases h), hm_a⟩
                          · intro B0 L0 hB0 hL0
                            exact wp_jump_state
                              (proj := fun st : BitVec 32 => (st, ()))
                              0#32 rfl
                              (hL0 _ _ ⟨by simp, fun _ hj => by simp at hj, hm_l1⟩)
                      · c0_hsteps!
                        obtain ⟨_, hmFin_m⟩ := kittenMemA_to_mem hm_l
                        refine solve_m5_post_finish hlen h256 hscr_len hscr_ge rfl hsi_m.inv hfuel_m
                          hsi_m.frame.nv hsi_m.frame.orig_nc hsi_m.frame.ante hsi_m.frame.nassump
                          hsi_m.frame.assump hsi_m.frame.perm hsi_m.frame.clAux
                          (fun _ => hsi_m.frame.core) (Or.inl rfl)
                          (fun h => absurd h (by decide)) ?_ hQ rfl
                        rw [← hkPtr_eq]; exact sep_ac hmFin_m
                    · c0_hsteps!
                      obtain ⟨_, hmFin_m⟩ := kittenMemA_to_mem hm_l
                      refine solve_m5_post_finish hlen h256 hscr_len hscr_ge rfl hsi_m.inv hfuel_m
                        hsi_m.frame.nv hsi_m.frame.orig_nc hsi_m.frame.ante hsi_m.frame.nassump
                        hsi_m.frame.assump hsi_m.frame.perm hsi_m.frame.clAux
                        (fun _ => hsi_m.frame.core) (Or.inl rfl)
                        (fun h => absurd h (by decide)) ?_ hQ rfl
                      rw [← hkPtr_eq]; exact sep_ac hmFin_m

end LeanQbe.T.Examples.Kissat.FullM5KittenDefFix
