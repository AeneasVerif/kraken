module

public import LeanQbe.T.Examples.Kissat.FullM7HotTernary
public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.FullCongLemmas2
public import LeanQbe.T.Examples.Kissat.FullOneLitConflLemmas
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Examples.Kissat.FullArena
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat M7 Hot-Loop Proofs: `full_has_ternary_m7` (`FullM7HotTernaryProof`)

M1-clean verification (`public section`, `0` `@[expose]`, `0` `import all`) for
`LeanQbe.T.Examples.Kissat.FullM7HotTernary`:
1. `full_has_ternary_m7_wp` and drop-in `m7HasTernaryFn_wp` proving exact canonical
   `Full.fullHasTernarySpec`.
2. Closed `1`-row `m7HotTernarySpecTable`, `m7HotTernaryEnv`, `m7HotTernaryEnv_noExit`,
   `m7HotTernary_tableImpl`, and `m7HotTernary_moduleOk`.
3. Concrete `Mem 64` UNSAT non-vacuity (`nv_m7_has_ternary`, `XPost := False`, `nvOneLitF0.Unsat`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7HotTernary

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

section HasTernaryM7

open FullCongSpecs FullCongHelpers
open scoped FullArenaTactics FullCongTactics

private theorem ht_slice_pop_step {F_cur : List (List Nat)} {k : FullCoreState} {a p rem : Nat}
    (hslice : if k.dense_mode = 0#64 then WatchSliceOk F_cur k a p rem
      else DenseWatchSliceOk F_cur k a p rem) (hpos : 0 < rem) :
    ∃ w0 : BitVec 32, k.wstk[p]? = some w0 ∧
      ((w0 &&& 0x80000000#32) ≠ 0#32 ∧
        (if k.dense_mode = 0#64 then WatchSliceOk F_cur k a (p + 1) (rem - 1)
         else DenseWatchSliceOk F_cur k a (p + 1) (rem - 1)) ∨
       (w0 &&& 0x80000000#32) = 0#32 ∧ 2 ≤ rem ∧
        ∃ cr : BitVec 32, k.wstk[p + 1]? = some cr ∧ cr.toNat ∈ fullArenaClauseRefsCore k ∧
        (if k.dense_mode = 0#64 then WatchSliceOk F_cur k a (p + 2) (rem - 2)
         else DenseWatchSliceOk F_cur k a (p + 2) (rem - 2))) := by
  by_cases hdm : k.dense_mode = 0#64 <;> simp only [hdm, ↓reduceIte] at hslice ⊢
  · cases hslice with
    | empty => omega
    | bin hp hf _ _ _ hrest => exact ⟨_, hp, Or.inl ⟨hf, hrest⟩⟩
    | large hp hp1 hf _ href hrest => exact ⟨_, hp, Or.inr ⟨hf, by omega, _, hp1, href, hrest⟩⟩
  · cases hslice with
    | empty => omega
    | bin hp hf _ _ _ hrest => exact ⟨_, hp, Or.inl ⟨hf, hrest⟩⟩
    | occ hp hp1 hf _ _ href hrest => exact ⟨_, hp, Or.inr ⟨hf, by omega, _, hp1, href, hrest⟩⟩

private theorem ht_ternary_of_unassigned_hits {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hlen : s.LengthsOk c)
    (hw : FullWitnessInv c F0 F_cur s.core) (hnd : Full.FullArenaVarsNodup s)
    (_hcl0 : s.core.cur_level = 0) {cr : Nat} {a b cl : BitVec 32}
    (hcr : cr ∈ fullArenaClauseRefs s) (hng : fullArenaClauseGarb s cr = false)
    (hnosat : ∀ k < fullArenaClauseSizeCore s.core cr,
      s.core.vals[(s.core.arena[cr + 3 + k]?.getD 0#32).toNat]?.getD 0#8 ≠ 1#8)
    (hcnt : ((fullArenaClauseLits s cr).filter (fun l => s.core.vals[l]?.getD 0#8 == 0#8)).length =
      3)
    (ha : a.toNat ∈ (fullArenaClauseLits s cr).filter (fun l => s.core.vals[l]?.getD 0#8 == 0#8))
    (hb : b.toNat ∈ (fullArenaClauseLits s cr).filter (fun l => s.core.vals[l]?.getD 0#8 == 0#8))
    (hc : cl.toNat ∈ (fullArenaClauseLits s cr).filter (fun l => s.core.vals[l]?.getD 0#8 == 0#8))
    (hab : a ≠ b) (hac : a ≠ cl) (hbc : b ≠ cl) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [a.toNat, b.toNat, cl.toNat]) := by
  have hwf := hw.arena.refs_wf cr hcr
  have hbd : cr + 3 + fullArenaClauseSizeCore s.core cr ≤ s.core.arena.length := by
    have := hlen.core_ok.arena_len_le; have := hlen.core_ok.arena_len_arr; omega
  have hnd_lits : (fullArenaClauseLits s cr).Nodup := nodup_of_map_nodup (hnd cr hcr hng)
  let unass := (fullArenaClauseLits s cr).filter (fun l => s.core.vals[l]?.getD 0#8 == 0#8)
  have hsub := nodup_len3_subset (hnd_lits.filter _) hcnt ha hb hc
    (fun h => hab (BitVec.eq_of_toNat_eq h))
    (fun h => hac (BitVec.eq_of_toNat_eq h))
    (fun h => hbc (BitVec.eq_of_toNat_eq h))
  refine entails_of_eval_mem fun α hα => ?_
  have hsat_cl := CNF.entails_clause_def.mp (hw.arena.entails cr hcr hng) α hα
  rw [← clauseEvalVal_iff, clauseEvalVal, List.any_eq_true] at hsat_cl
  obtain ⟨l, hl_mem, hl_true⟩ := hsat_cl
  have hl_lt : l < 2 * s.core.cur_vars := hw.arena.lits_lt cr hcr hng l hl_mem
  have hv_dom := hw.vals_domain l hl_lt
  obtain ⟨k, hk_lt, hget_k⟩ := (mem_fullArenaClauseLitsCore_iff hbd).mp hl_mem
  have hne1 : s.core.vals[l]?.getD 0#8 ≠ 1#8 := by
    have h := hnosat k hk_lt
    have hget_a :
        s.core.arena[cr + 3 + k]?.getD 0#32 = s.core.arena[cr + 3 + k]'(by omega) := by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    rwa [hget_a, hget_k] at h
  rcases hv_dom with hv0 | hv1 | hvm1
  · have hl_un : l ∈ unass := List.mem_filter.mpr ⟨hl_mem, by simp [hv0]⟩
    rcases hsub l hl_un with rfl | rfl | rfl
    · exact ⟨a.toNat, by simp, hl_true⟩
    · exact ⟨b.toNat, by simp, hl_true⟩
    · exact ⟨cl.toNat, by simp, hl_true⟩
  · exact absurd hv1 hne1
  · exfalso
    obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff l hl_lt).mp hvm1
    have hlvl0 : (s.core.lvl[(s.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
      have := hw.lvl_le i hi; omega
    have hunit := hw.level0_sound i hi hlvl0; rw [heq] at hunit
    have hsat_u := CNF.entails_clause_def.mp hunit α hα
    rw [← clauseEvalVal_iff, clauseEvalVal] at hsat_u; have hln : l ^^^ 1 = litNeg l := rfl
    simp only [List.any_cons, List.any_nil, Bool.or_false, hln, evalLitVal_litNeg,
      hl_true] at hsat_u
    cases hsat_u

private theorem ht_m7_take_step {s : FullState} {cr sz : Nat}
    (hlen : fullArenaClauseSizeCore s.core cr = sz)
    (hbd : cr + 3 + sz ≤ s.core.arena.length) {i : Nat} (hi : i < sz) :
    (fullArenaClauseLits s cr).take (i + 1) =
      (fullArenaClauseLits s cr).take i ++ [(s.core.arena[cr + 3 + i]'(by omega)).toNat] := by
  have hlen_l : (fullArenaClauseLits s cr).length = sz := by
    unfold fullArenaClauseLits fullArenaClauseLitsCore
    simp only [List.length_map, List.length_take, List.length_drop]; omega
  have hget_l : (fullArenaClauseLits s cr)[i]'(by omega) =
      (s.core.arena[cr + 3 + i]'(by omega)).toNat := by
    unfold fullArenaClauseLits fullArenaClauseLitsCore
    simp [List.getElem_map, List.getElem_take, List.getElem_drop]
  rw [List.take_succ_eq_append_getElem (by omega), hget_l]

private theorem ht_m7_take_all {s : FullState} {cr sz : Nat}
    (hlen : fullArenaClauseSizeCore s.core cr = sz)
    (_hbd : cr + 3 + sz ≤ s.core.arena.length) :
    (fullArenaClauseLits s cr).take sz = fullArenaClauseLits s cr := by
  apply List.take_of_length_le
  unfold fullArenaClauseLits fullArenaClauseLitsCore
  simp only [List.length_map, List.length_take, List.length_drop]; omega

private theorem ht_m7_filt_zero {s : FullState} {cr l i : Nat}
    (htk : (fullArenaClauseLits s cr).take (i + 1) = (fullArenaClauseLits s cr).take i ++ [l])
    (hv0 : s.core.vals[l]?.getD 0#8 = 0#8) :
    ((fullArenaClauseLits s cr).take (i + 1)).filter
      (fun x => s.core.vals[x]?.getD 0#8 == 0#8) =
    ((fullArenaClauseLits s cr).take i).filter
      (fun x => s.core.vals[x]?.getD 0#8 == 0#8) ++ [l] := by
  rw [htk, List.filter_append, List.filter_cons, hv0]; simp

private theorem ht_m7_filt_nz {s : FullState} {cr l i : Nat}
    (htk : (fullArenaClauseLits s cr).take (i + 1) = (fullArenaClauseLits s cr).take i ++ [l])
    (hv0 : s.core.vals[l]?.getD 0#8 ≠ 0#8) :
    ((fullArenaClauseLits s cr).take (i + 1)).filter
      (fun x => s.core.vals[x]?.getD 0#8 == 0#8) =
    ((fullArenaClauseLits s cr).take i).filter
      (fun x => s.core.vals[x]?.getD 0#8 == 0#8) := by
  rw [htk, List.filter_append, List.filter_cons,
    show (s.core.vals[l]?.getD 0#8 == 0#8) = false from by
      cases heq : (s.core.vals[l]?.getD 0#8 == 0#8)
      · rfl
      · exact absurd (beq_iff_eq.mp heq) hv0]
  simp

private theorem bv32_or_and_ne_zero {x y m : BitVec 32} (h : ((x ||| y) &&& m) ≠ 0#32) :
    (x &&& m) ≠ 0#32 ∨ (y &&& m) ≠ 0#32 := by
  by_cases hx : (x &&& m) = 0#32
  · right
    intro hy
    apply h
    apply BitVec.eq_of_getElem_eq
    intro i hi
    have hxi := congrArg (fun v : BitVec 32 => v[i]) hx
    have hyi := congrArg (fun v : BitVec 32 => v[i]) hy
    simp only [BitVec.getElem_and, BitVec.getElem_zero] at hxi hyi
    simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_zero]
    cases hmi : m[i] <;> simp_all
  · exact Or.inl hx

private theorem bv32_or2_and4_zero {x : BitVec 32} (hx : (x &&& 4#32) = 0#32) :
    ((x ||| 2#32) &&& 4#32) = 0#32 := by
  apply BitVec.eq_of_getElem_eq; intro i hi
  have hxi := congrArg (fun v : BitVec 32 => v[i]) hx
  simp only [BitVec.getElem_and, BitVec.getElem_zero] at hxi
  simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_zero]
  have h24 : ((2#32 : BitVec 32)[i] && (4#32 : BitVec 32)[i]) = false := by
    have h0 : (2#32 &&& 4#32 : BitVec 32) = 0#32 := by decide
    have h1 := congrArg (fun v : BitVec 32 => v[i]) h0
    rw [BitVec.getElem_and, BitVec.getElem_zero] at h1
    exact h1
  rw [Bool.and_or_distrib_right, hxi, h24]; rfl

private theorem ht_mask_hit {xs : List Nat} {l x : BitVec 32} {mask hit bit : BitVec 32}
    (hm : ((mask ||| hit) &&& bit) ≠ 0#32)
    (hprev : (mask &&& bit) ≠ 0#32 → x.toNat ∈ xs)
    (hcur : (hit &&& bit) ≠ 0#32 → l = x) :
    x.toNat ∈ xs ++ [l.toNat] := by
  rw [List.mem_append]
  rcases bv32_or_and_ne_zero hm with h1 | h2
  · exact Or.inl (hprev h1)
  · exact Or.inr (by simp [hcur h2])

/-- **M7 Hot-Loop `full_has_ternary_m7`**: proves exact canonical `Full.fullHasTernarySpec`
with hoisted `distinct`, single-read `vals[l]`, LSR pointer `ci`, and `mask` early-exit. -/
theorem full_has_ternary_m7_wp (Γ : Env) :
    ∀ args m Q X, Full.fullHasTernarySpec args m Q X →
      Func.wp Γ full_has_ternary_m7_body args m Q X := by
  rintro ⟨h, a, b, cl, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd, hcl0, ha_lt, hm0, hQ⟩
  have hmx := c.hmaxv; have hwc := c.hwcap; have hac := c.harena
  unfold dimacsBound at hmx hwc hac; have hcl := hlen.core_ok
  have hcv_le := hcl.cur_vars_le; have hwvl := hcl.wvec_len
  have hwsl := hcl.wstk_len_arr; have hwle := hcl.wlen_le
  have harl := hcl.arena_len_arr; have hale := hcl.arena_len_le; have hvl := hcl.vals_len
  have ha_v : a.toNat < s.core.vals.length := by omega
  have hnl_eq : (BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat)).toNat = 2 * s.core.cur_vars := by
    rw [BitVec.toNat_shiftLeft, bv64_ofNat_toNat (by omega)]
    simp [Nat.shiftLeft_eq]; omega
  have ha_shl1 : (a.setWidth 64 <<< (1 : Nat) + 1#64).toNat = 2 * a.toNat + 1 := by
    rw [BitVec.toNat_add, bv64_shl1_toNat, bv_zext32_toNat]; bv_omega
  fc_to_group
  fc_split
  · fc_to_group; exact hQ false (fun h => by cases h)
  · refine wp_join_group (ts := [i32, i32])
      (fun (scan1, min1, ()) m1 =>
        m1 = m0 ∧ scan1.toNat < 2 * s.core.cur_vars ∧
        min1 = s.core.wvec[2 * scan1.toNat + 1]?.getD 0#32) ?_ ?_
    · rintro _ ⟨scan1, min1, ⟨⟩⟩ m1 ⟨hm1, hscan1_lt, hmin1_eq⟩
      subst m1
      fc_to_group
      refine wp_join_group (ts := [i32, i32])
        (fun (scan, min_sz, ()) m1 =>
          m1 = m0 ∧ scan.toNat < 2 * s.core.cur_vars ∧
          min_sz = s.core.wvec[2 * scan.toNat + 1]?.getD 0#32) ?_ ?_
      · rintro _ ⟨scan, min_sz, ⟨⟩⟩ m1 ⟨hm1, hscan_lt, hmin_eq⟩
        subst m1
        have hw_bd := hw.watches.bounds scan.toNat hscan_lt
        have hshl : (scan.setWidth 64 <<< (1 : Nat)).toNat = 2 * scan.toNat := by
          rw [bv64_shl1_toNat, bv_zext32_toNat]; omega
        have hslice0 : if s.core.dense_mode = 0#64 then
              WatchSliceOk F_cur s.core scan.toNat (fullWatchOffCore s.core scan.toNat)
                (fullWatchSizeCore s.core scan.toNat)
            else DenseWatchSliceOk F_cur s.core scan.toNat (fullWatchOffCore s.core scan.toNat)
                (fullWatchSizeCore s.core scan.toNat) := by
          have hwat := hw.watches; unfold ModeWatchesInv at hwat
          by_cases hdm : s.core.dense_mode = 0#64 <;> simp only [hdm, ↓reduceIte] at hwat ⊢
          · exact hwat.slices scan.toNat hscan_lt
          · exact hwat.slices scan.toNat hscan_lt
        fc_split
        · fc_to_group; exact hQ false (fun h => by cases h)
        · fc_to_group
          refine wp_join_group (ts := [.bool]) (fun _ m1 => m1 = m0) ?_ ?_
          · rintro _ ⟨distinct, ⟨⟩⟩ m1 hm1
            subst m1
            fc_to_group
            generalize hoff_v :
              (s.core.wvec[(scan.setWidth 64 <<< (1 : Nat)).toNat]'(by omega)).setWidth 64 = off
            have hoff_n : off.toNat = fullWatchOffCore s.core scan.toNat := by
              rw [← hoff_v, bv_zext32_toNat]; unfold fullWatchOffCore
              rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
              exact congrArg BitVec.toNat (list_getElem_congr hshl (by omega) (by omega))
            have hwsz_n : min_sz.toNat = fullWatchSizeCore s.core scan.toNat := by
              rw [hmin_eq]; rfl
            have hend_n : (off + min_sz.setWidth 64).toNat = off.toNat + min_sz.toNat := by
              rw [BitVec.toNat_add, bv_zext32_toNat]
              exact Nat.mod_eq_of_lt (by omega)
            refine wp_loop_break_group (brkTs := [i64]) (lpTs := [i64])
              (fun _ mb => mb = m0)
              (fun rem (p, ()) ml =>
                ml = m0 ∧ p.toNat ≤ (off + min_sz.setWidth 64).toNat ∧
                rem = (off + min_sz.setWidth 64).toNat - p.toNat ∧
                (if s.core.dense_mode = 0#64 then
                   WatchSliceOk F_cur s.core scan.toNat p.toNat
                     ((off + min_sz.setWidth 64).toNat - p.toNat)
                 else DenseWatchSliceOk F_cur s.core scan.toNat p.toNat
                     ((off + min_sz.setWidth 64).toNat - p.toNat)))
              ?_ ?_ ?_
            · rintro _ ⟨_, ⟨⟩⟩ mb hmb; subst mb
              fc_to_group; exact hQ false (fun h => by cases h)
            · rintro B L rem ⟨p, ⟨⟩⟩ ml hB hL ⟨hml, hp_le, rfl, hslice⟩
              subst ml; fc_split
              · have hp_lt : p.toNat < (off + min_sz.setWidth 64).toNat := by bv_omega
                have hp_w : p.toNat < s.core.wstk.length := by omega
                obtain ⟨w0, hw0_get, hcase⟩ := ht_slice_pop_step hslice (by omega)
                have hw0_eq : s.core.wstk[p.toNat]'hp_w = w0 := by
                  rw [List.getElem?_eq_getElem hp_w] at hw0_get; exact Option.some.inj hw0_get
                have hp1_n : (p + 1#64).toNat = p.toNat + 1 := by bv_omega
                fc_split
                · rcases hcase with ⟨_, hrest⟩ | ⟨hf0, _⟩
                  · fc_to_group; exact hL ((off + min_sz.setWidth 64).toNat - (p + 1#64).toNat)
                      (p + 1#64, ()) m0 (by omega)
                      ⟨rfl, by omega, rfl, by simpa [hp1_n, Nat.sub_sub] using hrest⟩
                  · exfalso; rw [hw0_eq] at hc; exact hc hf0
                · rcases hcase with ⟨hf1, _⟩ | ⟨_, hrem2, cr, hcr_get, hcr_ref, hrest2⟩
                  · exfalso; rw [hw0_eq] at hc
                    change (w0 &&& 0x80000000#32) = 0#32 at hc
                    exact hf1 hc
                  · have hp1_n' : (p + 1).toNat = p.toNat + 1 := hp1_n
                    have hp1_w : (p + 1).toNat < s.core.wstk.length := by omega
                    have hcr_eq : s.core.wstk[(p + 1).toNat]'hp1_w = cr := by
                      rw [list_getElem_congr hp1_n' hp1_w (by omega)]
                      rw [List.getElem?_eq_getElem (by omega)] at hcr_get
                      exact Option.some.inj hcr_get
                    have hp1_m : (p.toNat + (1 : BitVec 64).toNat) % 2 ^ 64 = p.toNat + 1 :=
                      show (p.toNat + 1) % 2 ^ 64 = p.toNat + 1 from Nat.mod_eq_of_lt (by omega)
                    have hcr_m :
                        s.core.wstk[(p.toNat + (1 : BitVec 64).toNat) % 2 ^ 64]'(by omega) = cr :=
                      by
                        rw [list_getElem_congr hp1_m _ (by omega)]
                        rw [List.getElem?_eq_getElem (by omega)] at hcr_get
                        exact Option.some.inj hcr_get
                    have hcr_wf := hw.arena.refs_wf cr.toNat hcr_ref
                    have hp2_n : (p + 1#64 + 1#64).toNat = p.toNat + 2 := by bv_omega
                    have hcont2 : L (p + 1 + 1, ()) m0 :=
                      hL ((off + min_sz.setWidth 64).toNat - (p + 1#64 + 1#64).toNat)
                        (p + 1#64 + 1#64, ()) m0 (by omega)
                        ⟨rfl, by omega, rfl, by simpa [hp2_n, Nat.sub_sub] using hrest2⟩
                    have hcr_arr : cr.toNat < s.core.arena.length := by omega
                    have hcr2_m : (cr.toNat + (2 : BitVec 64).toNat) % 2 ^ 64 = cr.toNat + 2 :=
                      show (cr.toNat + 2) % 2 ^ 64 = cr.toNat + 2 from Nat.mod_eq_of_lt (by omega)
                    have hcr_w : ((s.core.wstk[(p + 1).toNat]'hp1_w).setWidth 64).toNat <
                        s.core.arena.length := by rw [hcr_eq, bv_zext32_toNat]; exact hcr_arr
                    have hcr2_w : ((s.core.wstk[(p + 1).toNat]'hp1_w).setWidth 64 + 2).toNat <
                        s.core.arena.length := by
                      rw [hcr_eq, BitVec.toNat_add, bv_zext32_toNat, hcr2_m]; omega
                    fc_split
                    · fc_split
                      · exact hcont2
                      · have hng_red := hc; clear hc; fc_split
                        · exact hcont2
                        · have hsz_ge3 := hc; clear hc
                          simp only [hcr_m, hcr2_m] at hng_red hsz_ge3
                          have hng : fullArenaClauseGarb s cr.toNat = false := by
                            unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
                            rw [List.getElem?_eq_getElem hcr_arr, Option.getD_some]
                            exact garb_false_of_and_480000 hng_red
                          let sz_bv := s.core.arena[cr.toNat + 2]'(by omega)
                          have hsz_eq : sz_bv.toNat = fullArenaClauseSizeCore s.core cr.toNat := by
                            unfold fullArenaClauseSizeCore
                            rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                          have hsz3 : 3 ≤ sz_bv.toNat := by
                            change ¬sz_bv.toNat < 3 at hsz_ge3; omega
                          have hsz_cv : sz_bv.toNat ≤ s.core.cur_vars := by
                            rw [hsz_eq]
                            exact fullArenaClauseSize_le_cur_vars hlen hw hnd hcr_ref hng
                          have hbd_ar : cr.toNat + 3 + sz_bv.toNat ≤ s.core.arena.length := by
                            omega
                          have hci0_n : (cr.setWidth 64 + 3#64).toNat = cr.toNat + 3 := by
                            rw [BitVec.toNat_add, bv_zext32_toNat,
                              show (3#64 : BitVec 64).toNat = 3 from rfl,
                              Nat.mod_eq_of_lt (by omega)]
                          have hcend_n :
                              (cr.setWidth 64 + 3#64 + sz_bv.setWidth 64).toNat =
                                cr.toNat + 3 + sz_bv.toNat := by
                            rw [BitVec.toNat_add, hci0_n, bv_zext32_toNat]
                            exact Nat.mod_eq_of_lt (by omega)
                          fc_to_group
                          let cend := (s.core.wstk[(p + 1).toNat]'hp1_w).setWidth 64 + 3 +
                            sz_bv.setWidth 64
                          have hcend_eq : cend.toNat = cr.toNat + 3 + sz_bv.toNat := by
                            dsimp only [cend]; rw [hcr_eq]; exact hcend_n
                          refine wp_loop_break_group
                            (brkTs := [i32, i32, i64])
                            (lpTs := [i32, i32, i64])
                            (fun (nf, mask, _, ()) mb2 =>
                              mb2 = m0 ∧
                              (mask = 7#32 →
                                (∀ k < sz_bv.toNat,
                                  s.core.vals[(s.core.arena[cr.toNat + 3 + k]?.getD
                                    0#32).toNat]?.getD 0#8 ≠ 1#8) ∧
                                nf.toNat = ((fullArenaClauseLits s cr.toNat).filter
                                  (fun l => s.core.vals[l]?.getD 0#8 == 0#8)).length ∧
                                a.toNat ∈ (fullArenaClauseLits s cr.toNat).filter
                                  (fun l => s.core.vals[l]?.getD 0#8 == 0#8) ∧
                                b.toNat ∈ (fullArenaClauseLits s cr.toNat).filter
                                  (fun l => s.core.vals[l]?.getD 0#8 == 0#8) ∧
                                cl.toNat ∈ (fullArenaClauseLits s cr.toNat).filter
                                  (fun l => s.core.vals[l]?.getD 0#8 == 0#8)))
                            (fun rem2 (nf, mask, ci, ()) mi =>
                              mi = m0 ∧
                              cr.toNat + 3 ≤ ci.toNat ∧ ci.toNat ≤ cend.toNat ∧
                              rem2 = cend.toNat - ci.toNat ∧ nf.toNat ≤ 3 ∧
                              (∀ k < ci.toNat - (cr.toNat + 3),
                                s.core.vals[(s.core.arena[cr.toNat + 3 + k]?.getD
                                  0#32).toNat]?.getD 0#8 ≠ 1#8) ∧
                              nf.toNat = (((fullArenaClauseLits s cr.toNat).take
                                (ci.toNat - (cr.toNat + 3))).filter
                                  (fun l => s.core.vals[l]?.getD 0#8 == 0#8)).length ∧
                              ((mask &&& 1#32) ≠ 0#32 →
                                a.toNat ∈ ((fullArenaClauseLits s cr.toNat).take
                                  (ci.toNat - (cr.toNat + 3))).filter
                                    (fun l => s.core.vals[l]?.getD 0#8 == 0#8)) ∧
                              ((mask &&& 2#32) ≠ 0#32 →
                                b.toNat ∈ ((fullArenaClauseLits s cr.toNat).take
                                  (ci.toNat - (cr.toNat + 3))).filter
                                    (fun l => s.core.vals[l]?.getD 0#8 == 0#8)) ∧
                              ((mask &&& 4#32) ≠ 0#32 →
                                cl.toNat ∈ ((fullArenaClauseLits s cr.toNat).take
                                  (ci.toNat - (cr.toNat + 3))).filter
                                    (fun l => s.core.vals[l]?.getD 0#8 == 0#8)))
                            ?_ ?_ ?_
                          · rintro _ ⟨nf, mask, _, ⟨⟩⟩ mb2 ⟨hmb2, hpost⟩
                            subst mb2; fc_split_fast
                            · have hnf3_eq : nf = 3#32 := beq_iff_eq.mp hc
                              clear hc; fc_split_fast
                              · have hm7_eq : mask = 7#32 := beq_iff_eq.mp hc
                                fc_to_group
                                obtain ⟨hnosat, hcnt, hha, hhb, hhc⟩ := hpost hm7_eq
                                have hnf3 : nf.toNat = 3 := by rw [hnf3_eq]; rfl
                                exact hQ true fun _ hab hac hbc =>
                                  ht_ternary_of_unassigned_hits hlen hw hnd hcl0 hcr_ref hng
                                    (hsz_eq ▸ hnosat) (hnf3 ▸ hcnt.symm)
                                    hha hhb hhc hab hac hbc
                              · exact hcont2
                            · exact hcont2
                          · rintro B2 L2 rem2 ⟨nf, mask, ci, ⟨⟩⟩ mi hB2 hL2
                              ⟨hmi, hci_lo, hci_le, rfl, hnf_le3,
                                hnosat_i, hcnt_i, hha_i, hhb_i, hhc_i⟩
                            subst mi; fc_split
                            · have hci_lt : ci.toNat < cend.toNat := by
                                simp only [hcr_m, hcr2_m] at hc
                                change ci.toNat < (cr.toNat + 3 + sz_bv.toNat) % 2 ^ 64 at hc
                                rw [hcend_eq]
                                have hmod : (cr.toNat + 3 + sz_bv.toNat) % 2 ^ 64 =
                                    cr.toNat + 3 + sz_bv.toNat := Nat.mod_eq_of_lt (by omega)
                                rw [hmod] at hc; exact hc
                              let idx := ci.toNat - (cr.toNat + 3)
                              have hci_eq : ci.toNat = cr.toNat + 3 + idx := by omega
                              have hidx_lt : idx < sz_bv.toNat := by omega
                              have hci_ar : ci.toNat < s.core.arena.length := by omega
                              have hci1_n : (ci + 1#64).toNat = ci.toNat + 1 := by
                                rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl]
                                exact Nat.mod_eq_of_lt (by omega)
                              let l := s.core.arena[ci.toNat]'hci_ar
                              have hl_eq_idx : l = s.core.arena[cr.toNat + 3 + idx]'(by omega) :=
                                list_getElem_congr hci_eq hci_ar (by omega)
                              have hl_mem : l.toNat ∈ fullArenaClauseLits s cr.toNat := by
                                rw [mem_fullArenaClauseLitsCore_iff (by omega), hl_eq_idx]
                                exact ⟨idx, by omega, rfl⟩
                              have hl_lt : l.toNat < 2 * s.core.cur_vars :=
                                hw.arena.lits_lt cr.toNat hcr_ref hng l.toNat hl_mem
                              have hl_v : (l.setWidth 64).toNat < s.core.vals.length := by
                                rw [bv_zext32_toNat]; omega
                              have htake_step := ht_m7_take_step hsz_eq.symm hbd_ar hidx_lt
                              rw [← hl_eq_idx] at htake_step
                              have hnf1_n : (nf + 1#32).toNat = nf.toNat + 1 :=
                                show (nf.toNat + 1) % 2 ^ 32 = nf.toNat + 1 from
                                  Nat.mod_eq_of_lt (by omega)
                              fc_split
                              · fc_to_group
                                exact hB2 (nf, 8#32, ci + 1#64, ()) m0
                                  ⟨rfl, fun h => absurd h (by decide)⟩
                              · have hne1_l : s.core.vals[l.toNat]?.getD 0#8 ≠ 1#8 := by
                                  rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                                  intro h1
                                  change (0#32).slt
                                    (BitVec.signExtend 32 (s.core.vals[l.toNat]'(by omega))) =
                                    false at hc
                                  rw [h1] at hc; exact absurd hc (by decide)
                                have hnosat_next : ∀ k < idx + 1,
                                    s.core.vals[(s.core.arena[cr.toNat + 3 + k]?.getD
                                      0#32).toNat]?.getD 0#8 ≠ 1#8 := fun k hk => by
                                  by_cases hki : k = idx
                                  · subst hki
                                    have ha_get :
                                        s.core.arena[cr.toNat + 3 + idx]?.getD 0#32 = l := by
                                      rw [List.getElem?_eq_getElem (by omega), Option.getD_some,
                                        hl_eq_idx]
                                    rw [ha_get]; exact hne1_l
                                  · exact hnosat_i k (by omega)
                                fc_to_group
                                refine wp_join_group (ts := [i32, i32])
                                  (fun (nf', mask', ()) m' =>
                                    m' = m0 ∧ nf'.toNat ≤ 3 ∧
                                    nf'.toNat = (((fullArenaClauseLits s cr.toNat).take
                                      (idx + 1)).filter
                                        (fun x => s.core.vals[x]?.getD 0#8 == 0#8)).length ∧
                                    ((mask' &&& 1#32) ≠ 0#32 →
                                      a.toNat ∈ ((fullArenaClauseLits s cr.toNat).take
                                        (idx + 1)).filter
                                          (fun x => s.core.vals[x]?.getD 0#8 == 0#8)) ∧
                                    ((mask' &&& 2#32) ≠ 0#32 →
                                      b.toNat ∈ ((fullArenaClauseLits s cr.toNat).take
                                        (idx + 1)).filter
                                          (fun x => s.core.vals[x]?.getD 0#8 == 0#8)) ∧
                                    ((mask' &&& 4#32) ≠ 0#32 →
                                      cl.toNat ∈ ((fullArenaClauseLits s cr.toNat).take
                                        (idx + 1)).filter
                                          (fun x => s.core.vals[x]?.getD 0#8 == 0#8)))
                                  ?_ ?_
                                · rintro _ ⟨nf', mask', ⟨⟩⟩ m'
                                    ⟨hm', hnf'_le3, hcnt', hha', hhb', hhc'⟩
                                  subst m'; fc_to_group
                                  have hk_next : (ci + 1#64).toNat - (cr.toNat + 3) = idx + 1 := by
                                    rw [hci1_n]; omega
                                  exact hL2 (cend.toNat - (ci + 1#64).toNat)
                                    (nf', mask', ci + 1#64, ()) m0 (by omega)
                                    ⟨rfl, by omega, by omega, rfl, hnf'_le3,
                                     hk_next ▸ hnosat_next, hk_next ▸ hcnt',
                                     hk_next ▸ hha', hk_next ▸ hhb', hk_next ▸ hhc'⟩
                                · intro J9 hJ9
                                  fc_split
                                  · have hval0 : s.core.vals[l.toNat]?.getD 0#8 = 0#8 := by
                                      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                                      have hdom := hw.vals_domain l.toNat hl_lt
                                      rw [List.getElem?_eq_getElem (by omega),
                                        Option.getD_some] at hdom
                                      change BitVec.signExtend 32
                                        (s.core.vals[l.toNat]'(by omega)) = 0#32 at hc
                                      rcases hdom with h | h | h
                                      · exact h
                                      · exfalso; rw [h] at hc; exact absurd hc (by decide)
                                      · exfalso; rw [h] at hc; exact absurd hc (by decide)
                                    have hfilt_step := ht_m7_filt_zero htake_step hval0
                                    fc_split
                                    · fc_to_group
                                      exact hB2 (nf + 1#32, 8#32, ci + 1#64, ()) m0
                                        ⟨rfl, fun h => absurd h (by decide)⟩
                                    · have hnf1_le3 : (nf + 1#32).toNat ≤ 3 := by
                                        rw [hnf1_n]
                                        change ¬(3#32 : BitVec 32).toNat <
                                          (nf.toNat + (1#32 : BitVec 32).toNat) % 2 ^ 32 at hc
                                        simp only [show (3#32 : BitVec 32).toNat = 3 from rfl,
                                          show (1#32 : BitVec 32).toNat = 1 from rfl] at hc
                                        omega
                                      fc_to_group
                                      refine wp_join_group (ts := [i32])
                                        (fun (h1, ()) m' => m' = m0 ∧
                                          ((h1 &&& 1#32) ≠ 0#32 → l = a) ∧
                                          (h1 &&& 2#32) = 0#32 ∧ (h1 &&& 4#32) = 0#32)
                                        ?_ ?_
                                      · rintro _ ⟨h1, ⟨⟩⟩ m' ⟨hm', h1a, h1b, h1c⟩
                                        subst m'; fc_to_group
                                        refine wp_join_group (ts := [i32])
                                          (fun (h2, ()) m' => m' = m0 ∧
                                            ((h2 &&& 1#32) ≠ 0#32 → l = a) ∧
                                            ((h2 &&& 2#32) ≠ 0#32 → l = b) ∧
                                            (h2 &&& 4#32) = 0#32)
                                          ?_ ?_
                                        · rintro _ ⟨h2, ⟨⟩⟩ m' ⟨hm', h2a, h2b, h2c⟩
                                          subst m'; fc_to_group
                                          refine wp_join_group (ts := [i32])
                                            (fun (h3, ()) m' => m' = m0 ∧
                                              ((h3 &&& 1#32) ≠ 0#32 → l = a) ∧
                                              ((h3 &&& 2#32) ≠ 0#32 → l = b) ∧
                                              ((h3 &&& 4#32) ≠ 0#32 → l = cl))
                                            ?_ ?_
                                          · rintro _ ⟨h3, ⟨⟩⟩ m' ⟨hm', h3a, h3b, h3c⟩
                                            subst m'; fc_to_group
                                            refine wp_join_group (ts := [])
                                              (fun _ m' => m' = m0) ?_ ?_
                                            · rintro _ ⟨⟩ m' hm'; subst m'; fc_to_group
                                              refine hJ9 (nf + 1#32, mask ||| h3, ()) m0
                                                ⟨rfl, hnf1_le3, ?_, ?_, ?_, ?_⟩
                                              · rw [hfilt_step, List.length_append, hnf1_n, hcnt_i]
                                                dsimp only [idx]; simp
                                              · intro hm
                                                rw [hfilt_step]
                                                exact ht_mask_hit hm hha_i h3a
                                              · intro hm
                                                rw [hfilt_step]
                                                exact ht_mask_hit hm hhb_i h3b
                                              · intro hm
                                                rw [hfilt_step]
                                                exact ht_mask_hit hm hhc_i h3c
                                            · intro J13 hJ13; fc_split_fast
                                              · fc_split_fast
                                                · fc_to_group
                                                  exact hB2 (nf + 1#32, 8#32, ci + 1#64, ()) m0
                                                    ⟨rfl, fun h => absurd h (by decide)⟩
                                                · fc_to_group; exact hJ13 () m0 rfl
                                              · fc_to_group; exact hJ13 () m0 rfl
                                          · intro J12 hJ12; fc_split_fast
                                            · fc_to_group; rw [beq_iff_eq] at hc
                                              refine hJ12 (h2 ||| 4#32, ()) m0 ⟨rfl, ?_, ?_, ?_⟩
                                              · intro h; rcases bv32_or_and_ne_zero h with h1 | h4
                                                · exact h2a h1
                                                · exfalso; exact h4 (by decide)
                                              · intro h; rcases bv32_or_and_ne_zero h with h1 | h4
                                                · exact h2b h1
                                                · exfalso; exact h4 (by decide)
                                              · intro _; exact hc
                                            · fc_to_group
                                              exact hJ12 (h2, ()) m0
                                                ⟨rfl, h2a, h2b, fun h => absurd h2c h⟩
                                        · intro J11 hJ11; fc_split_fast
                                          · fc_to_group; rw [beq_iff_eq] at hc
                                            refine hJ11 (h1 ||| 2#32, ()) m0 ⟨rfl, ?_, ?_, ?_⟩
                                            · intro h; rcases bv32_or_and_ne_zero h with hx | hy
                                              · exact h1a hx
                                              · exfalso; exact hy (by decide)
                                            · intro _; exact hc
                                            · exact bv32_or2_and4_zero h1c
                                          · fc_to_group
                                            exact hJ11 (h1, ()) m0 ⟨rfl, h1a,
                                              fun h => absurd h1b h, h1c⟩
                                      · intro J10 hJ10; fc_split_fast
                                        · fc_to_group; rw [beq_iff_eq] at hc
                                          exact hJ10 (1#32, ()) m0
                                            ⟨rfl, fun _ => hc, by decide, by decide⟩
                                        · fc_to_group
                                          exact hJ10 (0#32, ()) m0
                                            ⟨rfl, fun h => absurd (rfl : (0#32 &&& 1#32) = 0#32) h,
                                              by decide, by decide⟩
                                  · have hne0_l : s.core.vals[l.toNat]?.getD 0#8 ≠ 0#8 := by
                                      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                                      intro h0
                                      change BitVec.signExtend 32
                                        (s.core.vals[l.toNat]'(by omega)) ≠ 0#32 at hc
                                      exact hc (by rw [h0]; rfl)
                                    have hfilt_step := ht_m7_filt_nz htake_step hne0_l
                                    fc_to_group
                                    exact hJ9 (nf, mask, ()) m0
                                      ⟨rfl, hnf_le3,
                                       by rw [hfilt_step]; exact hcnt_i,
                                       by rw [hfilt_step]; exact hha_i,
                                       by rw [hfilt_step]; exact hhb_i,
                                       by rw [hfilt_step]; exact hhc_i⟩
                            · have hci_eq : ci.toNat = cend.toNat := by
                                simp only [hcr_m, hcr2_m] at hc
                                change ¬ci.toNat < (cr.toNat + 3 + sz_bv.toNat) % 2 ^ 64 at hc
                                have hmod : (cr.toNat + 3 + sz_bv.toNat) % 2 ^ 64 =
                                    cr.toNat + 3 + sz_bv.toNat := Nat.mod_eq_of_lt (by omega)
                                rw [hmod, ← hcend_eq] at hc; omega
                              have hk_eq : ci.toNat - (cr.toNat + 3) = sz_bv.toNat := by omega
                              have htake_all := hk_eq ▸ ht_m7_take_all hsz_eq.symm hbd_ar
                              rw [htake_all] at hcnt_i hha_i hhb_i hhc_i
                              rw [hk_eq] at hnosat_i
                              exact hB2 (nf, mask, ci, ()) m0 ⟨rfl, fun hm => by
                                subst hm
                                exact ⟨hnosat_i, hcnt_i, hha_i (by decide),
                                  hhb_i (by decide), hhc_i (by decide)⟩⟩
                          · intro B2 L2 hB2 hL2; fc_to_group
                            refine hL2 sz_bv.toNat
                              (0#32, 0#32, (s.core.wstk[(p + 1).toNat]'hp1_w).setWidth 64 + 3, ())
                              m0 ?_
                            have h0_eq :
                                ((s.core.wstk[(p + 1).toNat]'hp1_w).setWidth 64 + 3).toNat =
                                  cr.toNat + 3 := by
                              rw [hcr_eq]; exact hci0_n
                            dsimp only
                            refine ⟨rfl, by omega, by omega, by omega, by decide,
                              fun k hk => by rw [h0_eq, Nat.sub_self] at hk; simp at hk,
                              by rw [h0_eq, Nat.sub_self]; simp,
                              ?_, ?_, ?_⟩
                            · intro h; exfalso; exact h (by decide)
                            · intro h; exfalso; exact h (by decide)
                            · intro h; exfalso; exact h (by decide)
              · have hp_eq : p.toNat = (off + min_sz.setWidth 64).toNat := by bv_omega
                exact hB (p, ()) m0 rfl
            · intro B1 L1 hB1 hL1; fc_to_group
              exact hL1 min_sz.toNat (off, ()) m0
                ⟨rfl, by omega, by rw [hend_n]; omega,
                 by rw [hend_n, hoff_n, hwsz_n, Nat.add_sub_cancel_left]; exact hslice0⟩
          · intro Jd hJd
            c0_hsplit
            · c0_hsplit
              · c0_hsplit
                · c0_hsteps_nogrp; exact hJd (true, ()) m0 rfl
                · c0_hsteps_nogrp; exact hJd (false, ()) m0 rfl
              · c0_hsteps_nogrp; exact hJd (false, ()) m0 rfl
            · c0_hsteps_nogrp; exact hJd (false, ()) m0 rfl
      · intro Jc hJc
        c0_hsplit
        · have hcl_lt : cl.toNat < 2 * s.core.cur_vars := by omega
          have hcl_v : cl.toNat < s.core.vals.length := by omega
          have hcl_shl1 : (cl.setWidth 64 <<< (1 : Nat) + 1#64).toNat = 2 * cl.toNat + 1 := by
            rw [BitVec.toNat_add, bv64_shl1_toNat, bv_zext32_toNat]; bv_omega
          c0_hsplit
          · c0_hsteps_nogrp; exact hQ false (fun h => by cases h)
          · c0_hsteps_nogrp
            refine wp_join_group (ts := [i32, i32])
              (fun (scan, min_sz, ()) m1 =>
                m1 = m0 ∧ scan.toNat < 2 * s.core.cur_vars ∧
                min_sz = s.core.wvec[2 * scan.toNat + 1]?.getD 0#32)
              (fun _ xs m1 h => by c0_hsteps_nogrp; exact hJc xs m1 h)
              (fun Jc' hJc' => by
                c0_hsplit
                · have hix : (BitVec.setWidth 64 cl <<< 1 + 1).toNat = 2 * cl.toNat + 1 := by
                    rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, bv_zext32_toNat,
                      show (1 : BitVec 64).toNat = 1 from rfl, Nat.shiftLeft_eq]
                    omega
                  have hget_cl : s.core.wvec[(BitVec.setWidth 64 cl <<< 1 + 1).toNat]'(by omega) =
                      s.core.wvec[2 * cl.toNat + 1]?.getD 0#32 := by
                    rw [list_getElem_congr hix _ (by omega),
                      List.getElem?_eq_getElem (by omega), Option.getD_some]
                  rw [hget_cl]
                  exact hJc' (cl, s.core.wvec[2 * cl.toNat + 1]?.getD 0#32, ()) m0
                    ⟨rfl, hcl_lt, rfl⟩
                · exact hJc' (scan1, min1, ()) m0 ⟨rfl, hscan1_lt, hmin1_eq⟩)
        · exact hJc (scan1, min1, ()) m0 ⟨rfl, hscan1_lt, hmin1_eq⟩
    · intro Jb hJb
      c0_hsplit
      · have hb_lt : b.toNat < 2 * s.core.cur_vars := by omega
        have hb_v : b.toNat < s.core.vals.length := by omega
        have hb_shl1 : (b.setWidth 64 <<< (1 : Nat) + 1#64).toNat = 2 * b.toNat + 1 := by
          rw [BitVec.toNat_add, bv64_shl1_toNat, bv_zext32_toNat]; bv_omega
        c0_hsplit
        · c0_hsteps_nogrp; exact hQ false (fun h => by cases h)
        · c0_hsteps_nogrp
          refine wp_join_group (ts := [i32, i32])
            (fun (scan, min_sz, ()) m1 =>
              m1 = m0 ∧ scan.toNat < 2 * s.core.cur_vars ∧
              min_sz = s.core.wvec[2 * scan.toNat + 1]?.getD 0#32)
            (fun _ xs m1 h => by c0_hsteps_nogrp; exact hJb xs m1 h)
            (fun Jb' hJb' => by
              c0_hsplit
              · have hix : (BitVec.setWidth 64 b <<< 1 + 1).toNat = 2 * b.toNat + 1 := by
                  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, bv_zext32_toNat,
                    show (1 : BitVec 64).toNat = 1 from rfl, Nat.shiftLeft_eq]
                  omega
                have hget_b : s.core.wvec[(BitVec.setWidth 64 b <<< 1 + 1).toNat]'(by omega) =
                    s.core.wvec[2 * b.toNat + 1]?.getD 0#32 := by
                  rw [list_getElem_congr hix _ (by omega),
                    List.getElem?_eq_getElem (by omega), Option.getD_some]
                rw [hget_b]
                exact hJb' (b, s.core.wvec[2 * b.toNat + 1]?.getD 0#32, ()) m0
                  ⟨rfl, hb_lt, rfl⟩
              · have hix : (BitVec.setWidth 64 a <<< 1 + 1).toNat = 2 * a.toNat + 1 := by
                  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, bv_zext32_toNat,
                    show (1 : BitVec 64).toNat = 1 from rfl, Nat.shiftLeft_eq]
                  omega
                have hget_a : s.core.wvec[(BitVec.setWidth 64 a <<< 1 + 1).toNat]'(by omega) =
                    s.core.wvec[2 * a.toNat + 1]?.getD 0#32 := by
                  rw [list_getElem_congr hix _ (by omega),
                    List.getElem?_eq_getElem (by omega), Option.getD_some]
                rw [hget_a]
                exact hJb' (a, s.core.wvec[2 * a.toNat + 1]?.getD 0#32, ()) m0
                  ⟨rfl, ha_lt, rfl⟩)
      · have hix : (BitVec.setWidth 64 a <<< 1 + 1).toNat = 2 * a.toNat + 1 := by
          rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, bv_zext32_toNat,
            show (1 : BitVec 64).toNat = 1 from rfl, Nat.shiftLeft_eq]
          omega
        have hget_a : s.core.wvec[(BitVec.setWidth 64 a <<< 1 + 1).toNat]'(by omega) =
            s.core.wvec[2 * a.toNat + 1]?.getD 0#32 := by
          rw [list_getElem_congr hix _ (by omega),
            List.getElem?_eq_getElem (by omega), Option.getD_some]
        rw [hget_a]
        exact hJb (a, s.core.wvec[2 * a.toNat + 1]?.getD 0#32, ()) m0 ⟨rfl, ha_lt, rfl⟩

end HasTernaryM7

/-! ## 2. Closed `1`-Row `ModuleOk`, Drop-in `m7HasTernaryFn_wp`, & Concrete UNSAT NV -/

/-- Closed `1`-row spec table for `m7HotTernaryModule` (`noExit = true`). -/
def m7HotTernarySpecTable : List SpecEntry :=
  [ .ofFn full_has_ternary_m7 Full.fullHasTernarySpec true ]

/-- Executable contract environment for `m7HotTernaryModule`. -/
def m7HotTernaryEnv : Env := Env.ofTable m7HotTernarySpecTable

theorem m7HotTernarySpecTable_nodup :
    (m7HotTernarySpecTable.map SpecEntry.name).Nodup := by
  decide

theorem m7HotTernarySpecTable_sigs :
    m7HotTernarySpecTable.map (fun e => (e.name, e.as, e.rs)) =
      m7HotTernary_fns.map (fun f => (f.name, f.as, f.rs)) := by
  simp only [m7HotTernarySpecTable, m7HotTernary_fns, SpecEntry.ofFn, List.map_cons,
    List.map_nil, full_has_ternary_m7]

theorem m7HotTernaryEnv_noExit :
    ∀ f as bs xs m Q X X',
      m7HotTernaryEnv f as bs xs m Q X → m7HotTernaryEnv f as bs xs m Q X' :=
  Env.ofTable_noExit fun e he => by
    simp only [m7HotTernarySpecTable, List.mem_singleton] at he
    subst he; rfl

theorem m7HotTernary_allFns_wf : AllFns Fn.Wf m7HotTernaryModule.fns :=
  ⟨full_has_ternary_m7_wf, trivial⟩

theorem m7HotTernary_tableImpl :
    TableImpl m7HotTernaryEnv m7HotTernaryModule.fns m7HotTernarySpecTable :=
  ⟨SpecEntry.Impl.of (full_has_ternary_m7_wp m7HotTernaryEnv), trivial⟩

/-- Whole-module WP correctness theorem for `m7HotTernaryModule` under `m7HotTernaryEnv`. -/
theorem m7HotTernary_moduleOk : ModuleOk m7HotTernaryEnv m7HotTernaryModule :=
  Env.ofTable_moduleOk m7HotTernary_acyclic m7HotTernary_allFns_wf m7HotTernary_tableImpl

/-- Drop-in WP correctness for `m7HasTernaryFn` (`Full.fullHasTernarySpec`). -/
theorem m7HasTernaryFn_wp (Γ : Env) :
    ∀ args m Q X, Full.fullHasTernarySpec args m Q X →
      Func.wp Γ m7HasTernaryFn.body args m Q X :=
  full_has_ternary_m7_wp Γ

private theorem nvM7Hot_unsat : nvOneLitF0.Unsat := by
  rw [CNF.unsat_iff_not_sat]
  intro α hα
  have h0 : (cnfClause [0]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _
      (CNF.Internal.mem_iff.mpr (by dsimp only [nvOneLitF0]; simp [cnfOfClauses]))
  have h1 : (cnfClause [1]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _
      (CNF.Internal.mem_iff.mpr (by dsimp only [nvOneLitF0]; simp [cnfOfClauses]))
  rw [CNF.Clause.sat_iff_exists_mem_eq] at h0 h1
  obtain ⟨⟨v0, p0⟩, hm0, he0⟩ := h0; obtain ⟨⟨v1, p1⟩, hm1, he1⟩ := h1
  rw [mem_cnfClause_iff] at hm0 hm1
  simp only [List.mem_singleton] at hm0 hm1
  cases p0 <;> cases p1 <;> simp [litOfLiteral, mkLit] at hm0 hm1
  · have hv0 : v0 = 0 := by omega
    have hv1 : v1 = 0 := by omega
    subst hv0 hv1; dsimp only at he0 he1; rw [he0] at he1; cases he1
  · omega

private theorem nvM7Hot_entails_0 :
    (cnfOfClauses [[0], [1]]).EntailsClause (cnfClause [0]) := by
  rw [CNF.entails_clause_def]; intro α hα
  exact (CNF.sat_iff_all_mem_sat.mp hα) _ (CNF.Internal.mem_iff.mpr (by simp [cnfOfClauses]))

private theorem nvM7Hot_witness :
    FullWitnessInv nvOneLitCfg nvOneLitF0 [[0], [1]] nvOneLitState.core := by
  have hrefs : fullArenaClauseRefsCore nvOneLitState.core = [] := rfl
  have hcv : nvOneLitState.core.cur_vars = 1 := rfl
  have hte : nvOneLitState.core.trail_end = 1 := rfl
  have hcl : nvOneLitState.core.cur_level = 0 := rfl
  have hdm : nvOneLitState.core.dense_mode = 0#64 := rfl
  have hwat : ModeWatchesInv [[0], [1]] nvOneLitState.core := by
    unfold ModeWatchesInv; rw [ite_eq_left hdm]
    refine WatchesInv.of_slices (fun l hl => ?_) (fun l hl hp => ?_)
      (fun l1 _ h1 _ _ hp => ?_) (fun l hl => ?_)
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> decide
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
        simp [fullWatchSizeCore, nvOneLitState] at hp
    · rw [hcv] at h1; rcases (by omega : l1 = 0 ∨ l1 = 1) with rfl | rfl <;>
        simp [fullWatchSizeCore, nvOneLitState] at hp
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
        exact WatchSliceOk.empty
  exact
    { ext_sound := ⟨(varsBoundedBool_iff 1 [[0], [1]]).mp rfl, id⟩
      inconsistent_sound := fun h => absurd rfl h
      arena := ⟨Or.inl rfl, fun r hr => by simp [hrefs] at hr,
        fun r hr => by simp [hrefs] at hr,
        fun r hr => by simp [hrefs] at hr, fun r hr => by simp [hrefs] at hr⟩
      watches := hwat
      cur_level_le := Nat.zero_le _
      trail_lits_lt := fun i hi => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); decide
      trail_vars_nodup := fun i j hi hj _ => by rw [hte] at hi hj; omega
      vals_domain := fun l hl => by
        rw [hcv] at hl
        rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> simp [nvOneLitState]
      vals_true_iff := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · exact ⟨fun _ => ⟨0, Nat.zero_lt_one, rfl⟩, fun _ => rfl⟩
        · constructor
          · intro h; cases h
          · rintro ⟨i, hi, h⟩; rw [hte] at hi; obtain rfl : i = 0 := (by omega); cases h
      vals_false_iff := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · constructor
          · intro h; cases h
          · rintro ⟨i, hi, h⟩; rw [hte] at hi; obtain rfl : i = 0 := (by omega); cases h
        · exact ⟨fun _ => ⟨0, Nat.zero_lt_one, rfl⟩, fun _ => rfl⟩
      lvl_le := fun i hi => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact Nat.le_refl 0
      dec_earliest := fun _ j _ hj _ hpos => by
        rw [hte] at hj; obtain rfl : j = 0 := (by omega); exact absurd hpos.1 (by decide)
      levels_inhabited := fun _ _ h2 => by rw [hcl] at h2; omega
      level0_sound := fun i hi _ => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact nvM7Hot_entails_0
      trail_pos_inv := fun i hi => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); rfl
      level0_rsn_none := fun i hi _ => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); rfl
      frame_trail_lt := fun L hL => by
        rw [hcl] at hL; obtain rfl : L = 0 := (by omega); decide
      frame_trail_mono := fun L1 L2 _ hL2 => by
        rw [hcl] at hL2; obtain rfl : L1 = 0 := (by omega)
        obtain rfl : L2 = 0 := (by omega); exact Nat.le_refl _
      frame_trail_before_lt := fun _ _ h2 => by rw [hcl] at h2; omega
      frame_dec_lt := fun _ _ h2 => by rw [hcl] at h2; omega
      reason_inv := fun i hi hne => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact absurd rfl hne
      reason_lit_mem := fun i hi hne => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact absurd rfl hne }

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_has_ternary_m7`. -/
theorem nv_m7_has_ternary :
    Func.wp m7HotTernaryEnv full_has_ternary_m7_body
      (nvOneLitCfg.hdr, 0#32, 0#32, 0#32, ()) nvOneLitMem
      (fun (ok, ()) _ => nvOneLitF0.Unsat ∧ (ok = true → (0#32 : BitVec 32) ≠ 0#32 → False))
      (fun _ _ _ _ => False) :=
  full_has_ternary_m7_wp m7HotTernaryEnv _ nvOneLitMem _ (fun _ _ _ _ => False)
    ⟨nvOneLitCfg, nvOneLitF0, [[0], [1]], nvOneLitState, emp, rfl, nvOneLit_lengths,
     nvM7Hot_witness,
     (fun r h _ => by
       change r ∈ fullArenaClauseRefsCore nvOneLitState.core at h
       have hn : fullArenaClauseRefsCore nvOneLitState.core = [] := rfl
       rw [hn] at h; cases h),
     rfl, (by decide), (by rw [sep_emp]; exact nvOneLitMem_ok),
     fun _ _ => ⟨nvM7Hot_unsat, fun _ hne => hne rfl⟩⟩

end LeanQbe.T.Examples.Kissat.FullM7HotTernary
