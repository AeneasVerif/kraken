module

public import LeanQbe.T.Examples.Kissat.FullM8SweepV2
public import LeanQbe.T.Examples.Kissat.FullM6SweepProofKitten2a

/-!
# Kissat `M8` `V3t2` Revived Sweep — `K6` Kernel `Func.wp` Proofs (`3/10`)

Purely additive `Func.wp` proofs for the 3 modified `K6` sub-solver functions in
`FullM8SweepV2`:
1. Shared `k[25]` (`hdrTail[0]`) load/store & invariant preservation lemmas for PRNG state.
2. `m8_k6_add_clause_wp : k6AddClauseSpec` (with `full_k6_add_ticks(k, 1ULL)`).
3. `m8_k6_propagate_wp : k6PropagateSpec` (`ticks++` before `vals[other]==1u` + `visits >> 4`).
4. `m8_k6_flip_wp : k6FlipSpec` (`visits >> 4`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM8SweepV2

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM4Sweep
open LeanQbe.T.Examples.Kissat.FullM6Sweep
open Kraken.Bedrock2.Test

open K6MemATactics K6PtrTactics
open scoped K6MemATactics K6PtrTactics

/-! ## 1. `k[25]` (`hdrTail[0]`) Load/Store & Preservation Helpers -/

/-- Update word `25` (`hdrTail[0]`) of `K6State` (used as isolated xorshift32 seed in `M8`). -/
@[expose] def k6PutHdr25 (ks : K6State) (v : BitVec 32) : K6State :=
  { ks with hdrTail := ks.hdrTail.set 0 v }

theorem k6ShapesOk_putHdr25 {L : K6Layout} {ks : K6State}
    (h : ks.ShapesOk L) (v : BitVec 32) : (k6PutHdr25 ks v).ShapesOk L :=
  { h with hdrTail_len := by simp [k6PutHdr25, h.hdrTail_len] }

private theorem k6_list_set_append_left {α : Type _} (a b : List α) {i : Nat} (v : α)
    (hi : i < a.length) : (a ++ b).set i v = a.set i v ++ b := by
  apply List.ext_getElem
  · simp
  · intro j hj _
    by_cases hji : j = i
    · subst hji
      rw [List.getElem_set_self (by simp; omega), List.getElem_append_left (by simp; omega),
        List.getElem_set_self]
    · rw [List.getElem_set_ne (Ne.symm hji)]
      by_cases hj_a : j < a.length
      · rw [List.getElem_append_left hj_a, List.getElem_append_left (by simp; omega),
          List.getElem_set_ne (Ne.symm hji)]
      · rw [List.getElem_append_right (by omega), List.getElem_append_right (by simp; omega)]
        simp

private theorem k6_list_set_append_right {α : Type _} (a b : List α) {i : Nat} (v : α)
    (hi : a.length ≤ i) : (a ++ b).set i v = a ++ b.set (i - a.length) v := by
  apply List.ext_getElem
  · simp
  · intro j hj _
    by_cases hji : j = i
    · subst hji
      rw [List.getElem_set_self, List.getElem_append_right hi,
        List.getElem_set_self (by simp at hj ⊢; omega)]
    · rw [List.getElem_set_ne (Ne.symm hji)]
      by_cases hj_a : j < a.length
      · rw [List.getElem_append_left hj_a, List.getElem_append_left hj_a]
      · rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega),
          List.getElem_set_ne (by omega)]

private theorem k6Hdr25_hdrWords_eq (ks : K6State) (v : BitVec 32) :
    k6HdrWords (k6PutHdr25 ks v) = (k6HdrWords ks).set 25 v := by
  dsimp only [k6HdrWords, k6PutHdr25]
  rw [k6_list_set_append_right _ _ v (by simp)]
  simp

theorem k6Hdr25_toSlab {L : K6Layout} {ks : K6State} (hsh : ks.ShapesOk L) (v : BitVec 32) :
    (k6PutHdr25 ks v).toSlab = ks.toSlab.set 25 v := by
  have hhlen : (k6HdrWords ks).length = 32 := by
    simp [k6HdrWords, hsh.hdrTail_len]
  have h1 : (k6PutHdr25 ks v).toSlab =
      k6HdrWords (k6PutHdr25 ks v) ++
        (ks.lvlArr ++ (ks.rsn ++ (ks.qprev ++ (ks.qnext ++ (ks.qstampArr ++ (ks.trl ++
          (ks.flags ++ (ks.ana ++ (ks.kl ++ (ks.assump ++ (ks.vals ++ (ks.whead ++
            (ks.wnext ++ (ks.wblit ++ (ks.clOff ++ (ks.clSz ++ ks.arena)))))))))))))))) := rfl
  have h2 : ks.toSlab =
      k6HdrWords ks ++
        (ks.lvlArr ++ (ks.rsn ++ (ks.qprev ++ (ks.qnext ++ (ks.qstampArr ++ (ks.trl ++
          (ks.flags ++ (ks.ana ++ (ks.kl ++ (ks.assump ++ (ks.vals ++ (ks.whead ++
            (ks.wnext ++ (ks.wblit ++ (ks.clOff ++ (ks.clSz ++ ks.arena)))))))))))))))) := rfl
  rw [h1, h2, k6_list_set_append_left (k6HdrWords ks) _ v (by omega), k6Hdr25_hdrWords_eq]

@[scoped c0_load] theorem load_k6_hdr25 {L : K6Layout} {kPtr : BitVec 64} {ks : K6State}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (K6MemA L kPtr ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 25 * 4) = some (ks.hdrTail[0]?.getD 0#32) := by
  obtain ⟨hsh, hm0⟩ := k6MemA_to_mem hm
  rw [k6Mem_eq_array kPtr hsh] at hm0
  have hhlen : (k6HdrWords ks).length = 32 := by simp [k6HdrWords, hsh.hdrTail_len]
  have hlt : 25 < ks.toSlab.length := by
    change 25 < (k6HdrWords ks ++ _).length
    rw [List.length_append, hhlen]; omega
  have hl := loadVal_array (t := i32) (by decide) hlt hm0
  rw [show (i32 : Ty).bytes = 4 from rfl,
    show BitVec.ofNat 64 (4 * 25) = BitVec.ofNat 64 25 * 4 from by decide] at hl
  have hget? : ks.toSlab[25]? = some (ks.hdrTail[0]?.getD 0#32) := by
    change (k6HdrWords ks ++ _)[25]? = _
    rw [List.getElem?_append_left (by omega)]
    dsimp only [k6HdrWords]
    rw [List.getElem?_append_right (by simp)]
    simp only [List.length_cons, List.length_nil]
    have h0 : 0 < ks.hdrTail.length := by rw [hsh.hdrTail_len]; omega
    rw [List.getElem?_eq_getElem h0, Option.getD_some]
  have hget : ks.toSlab[25]'hlt = ks.hdrTail[0]?.getD 0#32 := by
    have hs := List.getElem?_eq_getElem hlt
    rw [hs] at hget?; exact Option.some.inj hget?
  rwa [hget] at hl

@[scoped c0_store] theorem store_k6_hdr25 {L : K6Layout} {kPtr : BitVec 64} {ks : K6State}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hm : (K6MemA L kPtr ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 25 * 4) ∧
      (K6MemA L kPtr (k6PutHdr25 ks v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 25 * 4) v) := by
  obtain ⟨hsh, hm0⟩ := k6MemA_to_mem hm
  rw [k6Mem_eq_array kPtr hsh] at hm0
  have hhlen : (k6HdrWords ks).length = 32 := by simp [k6HdrWords, hsh.hdrTail_len]
  have hlt : 25 < ks.toSlab.length := by
    change 25 < (k6HdrWords ks ++ _).length
    rw [List.length_append, hhlen]; omega
  obtain ⟨hok, hst⟩ := store_array (t := i32) v (by decide) hlt hm0
  rw [show (i32 : Ty).bytes = 4 from rfl,
    show BitVec.ofNat 64 (4 * 25) = BitVec.ofNat 64 25 * 4 from by decide] at hok hst
  have hsh' := k6ShapesOk_putHdr25 hsh v
  rw [← k6Hdr25_toSlab hsh v, ← k6Mem_eq_array kPtr hsh'] at hst
  exact ⟨hok, k6Mem_to_amem hsh' hst⟩

theorem k6Set25_preserves_inv {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (hinv : K6Inv L P ks) (v : BitVec 32) : K6Inv L P (k6PutHdr25 ks v) :=
  { shapes := k6ShapesOk_putHdr25 hinv.shapes v
    clauses :=
      { acap_eq := hinv.clauses.acap_eq
        max_v_eq := hinv.clauses.max_v_eq
        max_orig_eq := hinv.clauses.max_orig_eq
        max_cl_eq := hinv.clauses.max_cl_eq
        nv_le := hinv.clauses.nv_le
        nc_le := hinv.clauses.nc_le
        alen_le := hinv.clauses.alen_le
        nassump_le := hinv.clauses.nassump_le
        nkl_le := hinv.clauses.nkl_le
        nana_le := hinv.clauses.nana_le
        cl_wf := hinv.clauses.cl_wf
        cl_mono := hinv.clauses.cl_mono
        incons_ok := hinv.clauses.incons_ok
        assump_ok := hinv.clauses.assump_ok
        flags_clean := hinv.clauses.flags_clean }
    watches := hinv.watches
    assign :=
      { trl_end_le := hinv.assign.trl_end_le
        prop_le := hinv.assign.prop_le
        unass_eq := hinv.assign.unass_eq
        vals_dom := hinv.assign.vals_dom
        vals_neg_iff := hinv.assign.vals_neg_iff
        vals_nz_iff_trl := hinv.assign.vals_nz_iff_trl
        trl_nodup := hinv.assign.trl_nodup
        trl_lt := hinv.assign.trl_lt
        trl_lvl_le := hinv.assign.trl_lvl_le
        unass_lvl_zero := hinv.assign.unass_lvl_zero
        trl_lvl_mono := hinv.assign.trl_lvl_mono
        dec_earliest := hinv.assign.dec_earliest
        lvl0_ok := hinv.assign.lvl0_ok }
    reasons := hinv.reasons }

theorem k6Set25_preserves_sync {ks : K6State} (hsync : K6TrailSynced ks) (v : BitVec 32) :
    K6TrailSynced (k6PutHdr25 ks v) := hsync

@[scoped bv_c0] theorem k6PutHdr25_nv (ks : K6State) (v : BitVec 32) :
    (k6PutHdr25 ks v).nv = ks.nv := rfl
@[scoped bv_c0] theorem k6PutHdr25_nc (ks : K6State) (v : BitVec 32) :
    (k6PutHdr25 ks v).nc = ks.nc := rfl
@[scoped bv_c0] theorem k6PutHdr25_lvl (ks : K6State) (v : BitVec 32) :
    (k6PutHdr25 ks v).lvl = ks.lvl := rfl
@[scoped bv_c0] theorem k6PutHdr25_trl_end (ks : K6State) (v : BitVec 32) :
    (k6PutHdr25 ks v).trl_end = ks.trl_end := rfl
@[scoped bv_c0] theorem k6PutHdr25_unass (ks : K6State) (v : BitVec 32) :
    (k6PutHdr25 ks v).unass = ks.unass := rfl
@[scoped bv_c0] theorem k6PutHdr25_incons (ks : K6State) (v : BitVec 32) :
    (k6PutHdr25 ks v).incons = ks.incons := rfl
@[scoped bv_c0] theorem k6PutHdr25_alen (ks : K6State) (v : BitVec 32) :
    (k6PutHdr25 ks v).alen = ks.alen := rfl
@[scoped bv_c0] theorem k6PutHdr25_acap (ks : K6State) (v : BitVec 32) :
    (k6PutHdr25 ks v).acap = ks.acap := rfl
@[scoped bv_c0] theorem k6PutHdr25_nassump (ks : K6State) (v : BitVec 32) :
    (k6PutHdr25 ks v).nassump = ks.nassump := rfl
@[scoped bv_c0] theorem k6PutHdr25_max_v (ks : K6State) (v : BitVec 32) :
    (k6PutHdr25 ks v).max_v = ks.max_v := rfl
@[scoped bv_c0] theorem k6PutHdr25_max_orig (ks : K6State) (v : BitVec 32) :
    (k6PutHdr25 ks v).max_orig = ks.max_orig := rfl
@[scoped bv_c0] theorem k6PutHdr25_max_cl (ks : K6State) (v : BitVec 32) :
    (k6PutHdr25 ks v).max_cl = ks.max_cl := rfl
@[scoped bv_c0] theorem k6PutHdr25_neq (ks : K6State) (v : BitVec 32) :
    (k6PutHdr25 ks v).neq = ks.neq := rfl
@[scoped bv_c0] theorem k6PutHdr25_assump (ks : K6State) (v : BitVec 32) :
    (k6PutHdr25 ks v).assump = ks.assump := rfl
@[scoped bv_c0] theorem k6PutHdr25_vals (ks : K6State) (v : BitVec 32) :
    (k6PutHdr25 ks v).vals = ks.vals := rfl

@[scoped c0_store] theorem store_full_k6_hdr25 {c : FullCfg} {L : K6Layout} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32)
    (hlen : s.scratch.scratch_buf.length = L.scrLen)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (L.kPtr c.pScratchBuf + BitVec.ofNat 64 25 * 4) ∧
      (FullMem c { s with scratch :=
          { s.scratch with scratch_buf := s.scratch.scratch_buf.set (L.k6Base + 25) v } } ⋆ R)
        (storeMem m i32 (L.kPtr c.pScratchBuf + BitVec.ofNat 64 25 * 4) v) := by
  have hm1 := hm
  rw [fullMem_eq_k6Frame hlen] at hm1
  let ks := K6State.ofSlab L (s.scratch.scratch_buf.drop L.k6Base)
  have hle : (s.scratch.scratch_buf.drop L.k6Base).length = L.k6Fixed + L.acap := by
    rw [List.length_drop, hlen]; unfold K6Layout.scrLen; omega
  have hle_le : L.k6Fixed ≤ (s.scratch.scratch_buf.drop L.k6Base).length := by omega
  have hsh : ks.ShapesOk L := K6State.shapesOk_ofSlab_eq (L := L)
    (xs := s.scratch.scratch_buf.drop L.k6Base) hle
  have hm2 : (K6MemA L (L.kPtr c.pScratchBuf) ks ⋆ (FullK6Frame c L s ⋆ R)) m :=
    k6Mem_to_amem hsh (sep_ac hm1)
  obtain ⟨hok, hst⟩ := store_k6_hdr25 v hm2
  refine ⟨hok, ?_⟩
  obtain ⟨hsh', hst0⟩ := k6MemA_to_mem hst
  have hst1 : (FullK6Frame c L s ⋆ K6Mem L (L.kPtr c.pScratchBuf) (k6PutHdr25 ks v) ⋆ R)
      (storeMem m i32 (L.kPtr c.pScratchBuf + BitVec.ofNat 64 25 * 4) v) := sep_ac hst0
  have hkbase : L.k6Base ≤ s.scratch.scratch_buf.length := by
    rw [hlen]; unfold K6Layout.scrLen; omega
  have hjm := fullMem_join_k6 hkbase hsh' hst1
  have hset_eq :
      s.scratch.scratch_buf.take L.k6Base ++ (k6PutHdr25 ks v).toSlab =
        s.scratch.scratch_buf.set (L.k6Base + 25) v := by
    rw [k6Hdr25_toSlab hsh v, show ks.toSlab = s.scratch.scratch_buf.drop L.k6Base from
      K6State.toSlab_ofSlab hle_le]
    have htk : (s.scratch.scratch_buf.take L.k6Base).length = L.k6Base :=
      List.length_take_of_le hkbase
    have hset :
        (s.scratch.scratch_buf.take L.k6Base ++ s.scratch.scratch_buf.drop L.k6Base).set
            (L.k6Base + 25) v =
          s.scratch.scratch_buf.take L.k6Base ++ (s.scratch.scratch_buf.drop L.k6Base).set 25 v := by
      rw [k6_list_set_append_right _ _ v (by omega), htk,
        show L.k6Base + 25 - L.k6Base = 25 by omega]
    rw [List.take_append_drop] at hset
    exact hset.symm
  rw [hset_eq] at hjm
  exact hjm

theorem k6WatchStep_putHdr_ticks (ks : K6State) (tk' cid l0 l1 : BitVec 32) :
    k6WatchStep (ks.putHdr .ticks tk') cid l0 l1 = (k6WatchStep ks cid l0 l1).putHdr .ticks tk' := by
  dsimp only [k6WatchStep, k6WatchStep0, K6State.putHdr, K6State.putArr]

/-! ## 2. `m8_k6_add_clause_wp` -/

private theorem bv32_setWidth_maxV (L : K6Layout) :
    BitVec.setWidth 32 (BitVec.ofNat 64 L.maxV) = L.mv32 := by
  unfold K6Layout.mv32; bv_omega
attribute [local bv_c0] bv32_setWidth_maxV

theorem m8_k6_add_clause_wp (Γ : Env)
    (hMaxV : M6EnvSpec Γ "full_m6_max_v" m6MaxVSpec)
    (hAddTicks : M6EnvSpec Γ "full_k6_add_ticks" k6AddTicksSpec)
    (hAssign : M6EnvSpec Γ "full_k6_assign" k6AssignSpec)
    (hWatch : M6EnvSpec Γ "full_k6_watch" k6WatchSpec) :
    ∀ args m Q X, k6AddClauseSpec args m Q X → Func.wp Γ full_k6_add_clause_body args m Q X := by
  rintro ⟨h, litsPtr, sz, ⟨⟩⟩ m Q X
    ⟨c, s, P, L, scr, xs, R, hhdr, hlen, hscr_eq, hscr_len, hmaxv, hinv, hsync, hlvl0, hsz_xs,
     hsz_lt28, hxlits, hent, hm, hQ⟩
  subst hhdr
  have hscr_klen : scr.length = L.scrLen := by
    rw [← hscr_eq, hlen.scratch_ok.scratch_buf_len, hscr_len]
  have hm_b := L.hmaxV; have hac_b := L.hacap
  have hcap_lt64 : c.scratch_cap < 2 ^ 64 := by
    rw [← hscr_len]
    dsimp only [K6Layout.scrLen, K6Layout.k6Base, K6Layout.k6Fixed, K6Layout.maxCl] at *
    unfold dimacsBound at hac_b
    omega
  let ks := k6StateOfScratch L scr
  have hsh : ks.ShapesOk L := hinv.shapes
  have hnv : ks.nv.toNat ≤ L.maxV := hinv.clauses.nv_le
  have hmv_eq_ks : ks.max_v = L.mv32 := hinv.clauses.max_v_eq
  have hmc_eq : ks.max_cl = BitVec.ofNat 32 L.maxCl := hinv.clauses.max_cl_eq
  have hca_eq : ks.acap = BitVec.ofNat 32 L.acap := hinv.clauses.acap_eq
  have hkbase : L.k6Base ≤ scr.length := by
    rw [hscr_klen]; unfold K6Layout.scrLen; omega
  have htoSlab_len : ∀ {ks' : K6State}, ks'.ShapesOk L →
      ks'.toSlab.length = L.k6Fixed + L.acap := fun hsh' => by
    simp [K6State.toSlab, k6HdrWords, hsh'.hdrTail_len, hsh'.lvlArr_len, hsh'.rsn_len,
      hsh'.qprev_len, hsh'.qnext_len, hsh'.qstampArr_len, hsh'.trl_len, hsh'.flags_len,
      hsh'.ana_len, hsh'.kl_len, hsh'.assump_len, hsh'.vals_len, hsh'.whead_len, hsh'.wnext_len,
      hsh'.wblit_len, hsh'.clOff_len, hsh'.clSz_len, hsh'.arena_len]
    dsimp only [K6Layout.k6Fixed, K6Layout.maxCl]; omega
  have hreorg : ∀ {ks' : K6State} {m' : Mem 64}, ks'.ShapesOk L →
      (K6MemA L (L.kPtr c.pScratchBuf) ks' ⋆
        (array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
          (array (t := i32) litsPtr xs ⋆
            (array (t := i32) c.pScratchBuf (scr.take L.k6Base) ⋆ R)))) m' →
      let scr' := scr.take L.k6Base ++ ks'.toSlab
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      scr'.length = c.scratch_cap ∧
      (∀ i < L.k6Base, scr'[i]? = scr[i]?) ∧
      (array64 (c.hdr + 32) (Full.hdrTailWords c s') ⋆ array (t := i32) c.pScratchBuf scr' ⋆
        array (t := i32) litsPtr xs ⋆ R) m' := by
    intro ks' m' hsh' hm' scr' s'
    have htk : (scr.take L.k6Base).length = L.k6Base :=
      List.length_take_of_le hkbase
    have hlen' : scr'.length = c.scratch_cap := by
      dsimp only [scr']
      rw [List.length_append, htk, htoSlab_len hsh']
      rw [← hscr_len]; dsimp only [K6Layout.scrLen]; omega
    have hpfx : ∀ i < L.k6Base, scr'[i]? = scr[i]? := fun i hi => by
      dsimp only [scr']
      rw [List.getElem?_append_left (by omega), List.getElem?_take_of_lt hi]
    exact ⟨hlen', hpfx, fullAddClause6_ka_to_mem hkbase hsh' hm'⟩
  have hof_slab : ∀ {ks' : K6State}, ks'.ShapesOk L →
      k6StateOfScratch L (scr.take L.k6Base ++ ks'.toSlab) = ks' := by
    intro ks' hsh'
    unfold k6StateOfScratch
    have htk : (scr.take L.k6Base).length = L.k6Base := List.length_take_of_le hkbase
    rw [List.drop_append, htk, Nat.sub_self, List.drop_zero,
      List.drop_eq_nil_of_le (by rw [htk]; exact Nat.le_refl _), List.nil_append,
      K6State.ofSlab_toSlab hsh']
  have hmA : (K6MemA L (L.kPtr c.pScratchBuf) ks ⋆
      (array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
        (array (t := i32) litsPtr xs ⋆
          (array (t := i32) c.pScratchBuf (scr.take L.k6Base) ⋆ R)))) m := by
    have hm1 := hm
    rw [array_scratch_eq_k6 hscr_klen] at hm1
    exact k6Mem_to_amem hsh (sep_ac hm1)
  have hscr_orig : scr.take L.k6Base ++ ks.toSlab = scr := by
    dsimp only [ks, k6StateOfScratch]
    have hle_d : L.k6Fixed ≤ (scr.drop L.k6Base).length := by
      rw [List.length_drop, hscr_klen]; unfold K6Layout.scrLen; omega
    rw [K6State.toSlab_ofSlab hle_d, List.take_append_drop]
  c0_hsteps_nogrp
  · k6_call hMaxV
    dsimp only [m6MaxVSpec]
    have hmv_eq : BitVec.ofNat 64 (k6MaxV (BitVec.ofNat 64 c.scratch_cap).toNat) =
        BitVec.ofNat 64 L.maxV := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcap_lt64, ← hmaxv]
    have hsw_mv : BitVec.setWidth 32 (BitVec.ofNat 64 L.maxV) = L.mv32 := by
      unfold K6Layout.mv32; bv_omega
    rw [hmv_eq]
    c0_hsteps_nogrp
    try simp only [hsw_mv]
    try rw [k6_ptr_base L c.pScratchBuf]
    try rw [k6_ptr_base_bv L c.pScratchBuf]
    c0_hsteps_nogrp
    try simp only [hsw_mv, k6_ptr_base, k6_ptr_base_bv]
    c0_hsplit
    · -- sz == 0
      have hsz0 : sz = 0#32 := ‹_›
      have hunsat : ∀ β, ¬ P β := by
        rw [hsz0] at hent; simp at hent; exact SemEntails.unsat_of_nil hent
      c0_hsteps!
      have hinv' := k6SetIncons_preserves_inv hinv hunsat
      have hmF := hreorg hinv'.shapes ‹_›
      exact hQ true _ _ hmF.1 hmF.2.1 (by rw [hof_slab hinv'.shapes]; exact hinv')
        (by rw [hof_slab hinv'.shapes]; exact hsync)
        (by rw [hof_slab hinv'.shapes]; k6_field; exact hlvl0)
        (by rw [hof_slab hinv'.shapes]; k6_field)
        (by rw [hof_slab hinv'.shapes]; k6_field)
        (by unfold k6AssumpLitsS k6AssumpLits; rw [hof_slab hinv'.shapes]; k6_field)
        (fun h => by cases h)
        (fun h2 => by rw [hsz0] at h2; simp at h2)
        (fun M _ hM htr => by
          rw [hof_slab hinv'.shapes]
          exact ⟨⟨fun c hc => hM.1 c hc, fun w hw => hM.2 w hw⟩, htr⟩) hmF.2.2
    · have hsz_pos : 0 < sz.toNat := by
        have hne0 : sz ≠ 0#32 := ‹_›
        have h0 : sz.toNat ≠ 0 := fun h => hne0 (BitVec.eq_of_toNat_eq h)
        omega
      have h0_xs : 0 < xs.length := by omega
      have hu_lt : (xs[0]'h0_xs).toNat < 2 * ks.nv.toNat := by
        have h := hxlits 0 hsz_pos
        rwa [List.getElem?_eq_getElem h0_xs, Option.getD_some] at h
      have hu_mv2 : (xs[0]'h0_xs).toNat < sz2V L := by unfold sz2V; omega
      try simp only [hsw_mv, k6_ptr_base]
      c0_hsteps_nogrp
      try simp only [hsw_mv, k6_ptr_base]
      c0_hsplit
      · -- sz == 1
        have hsz1 : sz = 1#32 := ‹_›
        have hent1 : SemEntails P [(xs[0]'h0_xs).toNat] := by
          have htk : (xs.take sz.toNat).map BitVec.toNat = [(xs[0]'h0_xs).toNat] := by
            rw [hsz1]; cases xs with | nil => simp at h0_xs | cons x _ => rfl
          rwa [htk] at hent
        c0_hsteps_nogrp
        try refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
        c0_hsplit
        · -- uv == 2u
          have hfals : ks.vals[(xs[0]'h0_xs).toNat]? = some 2#32 := by
            have hv_eq : ks.vals[(xs[0]'h0_xs).toNat]?.getD 0#32 = 2#32 := by simpa using ‹_›
            rw [List.getElem?_eq_getElem (by rw [hsh.vals_len]; exact hu_mv2),
              Option.getD_some] at hv_eq
            rw [List.getElem?_eq_getElem (by rw [hsh.vals_len]; exact hu_mv2), hv_eq]
          have hunsat : ∀ β, ¬ P β := SemEntails.unsat_of_falsified hent1 fun x hx => by
            simp at hx; subst hx; exact (k6_falsified_lvl0_entails hinv hlvl0 hu_lt hfals).2
          c0_hsteps!
          have hinv' := k6SetIncons_preserves_inv hinv hunsat
          have hmF := hreorg hinv'.shapes ‹_›
          exact hQ true _ _ hmF.1 hmF.2.1 (by rw [hof_slab hinv'.shapes]; exact hinv')
            (by rw [hof_slab hinv'.shapes]; exact hsync)
            (by rw [hof_slab hinv'.shapes]; k6_field; exact hlvl0)
            (by rw [hof_slab hinv'.shapes]; k6_field)
            (by rw [hof_slab hinv'.shapes]; k6_field)
            (by unfold k6AssumpLitsS k6AssumpLits; rw [hof_slab hinv'.shapes]; k6_field)
            (fun h => by cases h)
            (fun h2 => by rw [hsz1] at h2; simp at h2)
            (fun M _ hM htr => by
              rw [hof_slab hinv'.shapes]
              exact ⟨⟨fun c hc => hM.1 c hc, fun w hw => hM.2 w hw⟩, htr⟩) hmF.2.2
        · try refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
          c0_hsplit
          · -- uv == 0u
            have hun0 : ks.vals[(xs[0]'h0_xs).toNat]? = some 0#32 := by
              have hv_eq : ks.vals[(xs[0]'h0_xs).toNat]?.getD 0#32 = 0#32 := by simpa using ‹_›
              rw [List.getElem?_eq_getElem (by rw [hsh.vals_len]; exact hu_mv2),
                Option.getD_some] at hv_eq
              rw [List.getElem?_eq_getElem (by rw [hsh.vals_len]; exact hu_mv2), hv_eq]
            have hte_lt := k6_trl_end_lt_of_unassigned hsh hnv hinv.assign hu_lt (by simp [hun0])
            obtain ⟨hinv', hsync'⟩ := k6AssignStep_preserves_inv hinv hsync hu_lt hun0
              (fun _ => hent1) (fun hpos => by rw [hlvl0] at hpos; simp at hpos) (Or.inl rfl)
            k6_call hAssign
            refine ⟨L, ks, _, hsh, hmv_eq_ks,
              (by change (xs[0]'h0_xs).toNat < 2 * L.maxV; omega),
              (by omega), (k6MemA_to_mem hmA).2, fun m' hm' => ?_⟩
            c0_hsteps!
            have hmF := hreorg hinv'.shapes (k6Mem_to_amem hinv'.shapes hm')
            exact hQ true _ _ hmF.1 hmF.2.1 (by rw [hof_slab hinv'.shapes]; exact hinv')
              (by rw [hof_slab hinv'.shapes]; exact hsync')
              (by rw [hof_slab hinv'.shapes]; exact hlvl0)
              (by rw [hof_slab hinv'.shapes]; rfl) (by rw [hof_slab hinv'.shapes]; rfl)
              (by unfold k6AssumpLitsS k6AssumpLits; rw [hof_slab hinv'.shapes]; rfl)
              (fun h => by cases h)
              (fun h2 => by rw [hsz1] at h2; simp at h2)
              (fun M hxsM hM htr => by
                rw [hof_slab hinv'.shapes]
                refine ⟨⟨fun c hc => hM.1 c hc, fun w hw => hM.2 w hw⟩, fun l hl => ?_⟩
                unfold k6TrailLits k6AssignStep at hl
                dsimp only [K6State.putHdr, K6State.putArr] at hl
                have hte1 : (ks.trl_end + 1#32).toNat = ks.trl_end.toNat + 1 := by
                  have := L.hmaxV; bv_omega
                rw [hte1] at hl
                rw [List.mem_map] at hl; obtain ⟨b, hb, rfl⟩ := hl
                obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
                simp only [List.length_take, List.length_set] at hj
                have hj_lt : j < ks.trl_end.toNat + 1 := by omega
                simp only [List.getElem_take]
                by_cases hj_old : j < ks.trl_end.toNat
                · rw [List.getElem_set_ne (Nat.ne_of_gt hj_old)]
                  refine htr _ (List.mem_map.mpr ⟨(ks.trl.take ks.trl_end.toNat)[j]'(by
                    rw [List.length_take, hsh.trl_len, Nat.min_eq_left (by omega)]
                    exact hj_old), List.getElem_mem _, by simp only [List.getElem_take]; rfl⟩)
                · have hj_eq : j = ks.trl_end.toNat := by omega
                  subst hj_eq
                  rw [List.getElem_set_self]
                  have hx0 := hxsM 0 (by rw [hsz1]; decide)
                  rwa [List.getElem?_eq_getElem h0_xs, Option.getD_some] at hx0) hmF.2.2
          · -- uv == 1u
            c0_hsteps!
            exact hQ true scr m (hscr_klen.trans hscr_len) (fun _ _ => rfl) hinv hsync hlvl0
              rfl rfl rfl (fun h => by cases h) (fun h2 => by rw [hsz1] at h2; simp at h2)
              (fun _ _ hM htr => ⟨hM, htr⟩) (by simpa [← hscr_eq] using hm)
    · -- sz >= 2
      have hsz2 : 2 ≤ sz.toNat := by
        have hne0 : sz ≠ 0#32 := ‹_›; have hne1 : sz ≠ 1#32 := ‹_›
        have h0 : sz.toNat ≠ 0 := fun h => hne0 (BitVec.eq_of_toNat_eq h)
        have h1 : sz.toNat ≠ 1 := fun h => hne1 (BitVec.eq_of_toNat_eq h); omega
      try simp only [hsw_mv, k6_ptr_base]
      c0_hsplit
      · -- nc >= max_cl => false
        c0_hsteps!
        exact hQ false scr m (hscr_klen.trans hscr_len) (fun _ _ => rfl) hinv hsync hlvl0
          rfl rfl rfl (fun _ => rfl) (fun _ => ⟨rfl, rfl, rfl, rfl⟩)
          (fun _ _ hM htr => ⟨hM, htr⟩) (by simpa [← hscr_eq] using hm)
      · c0_hsplit
        · -- off + sz > acap => false
          c0_hsteps!
          exact hQ false scr m (hscr_klen.trans hscr_len) (fun _ _ => rfl) hinv hsync hlvl0
            rfl rfl rfl (fun _ => rfl) (fun _ => ⟨rfl, rfl, rfl, rfl⟩)
            (fun _ _ hM htr => ⟨hM, htr⟩) (by simpa [← hscr_eq] using hm)
        · have hmc_lt : L.maxCl < 2 ^ 32 := by unfold K6Layout.maxCl; omega
          have hnc_lt : ks.nc.toNat < L.maxCl := by
            have h1 : ks.nc.toNat < ks.max_cl.toNat := by omega
            rwa [hmc_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmc_lt] at h1
          have hcap_lt : L.acap < 2 ^ 28 := by unfold dimacsBound at hac_b; omega
          have hal_ks : ks.alen.toNat ≤ L.acap := hinv.clauses.alen_le
          have hca_n : ks.acap.toNat = L.acap := by
            rw [hca_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          have hsum_lt : ks.alen.toNat + sz.toNat < 2 ^ 32 := by omega
          have hoff_fit : ks.alen.toNat + sz.toNat ≤ L.acap := by
            have h1 : (ks.alen.toNat + sz.toNat) % 2 ^ 32 ≤ ks.acap.toNat := by omega
            rw [Nat.mod_eq_of_lt hsum_lt, hca_n] at h1
            exact h1
          c0_hsteps_nogrp
          refine wp_while_state
            (proj := fun st : BitVec 32 × List (BitVec 32) => (st.1, ()))
            (fun st => sz.toNat - st.1.toNat)
            (fun (i, ar') m' => i.toNat ≤ sz.toNat ∧ ar'.length = L.acap ∧
              (∀ j < ks.alen.toNat, ar'[j]? = ks.arena[j]?) ∧
              (∀ j < i.toNat, ar'[ks.alen.toNat + j]? = xs[j]?) ∧
              (K6MemA L (L.kPtr c.pScratchBuf) { ks with arena := ar' } ⋆
                (array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
                  (array (t := i32) litsPtr xs ⋆
                    (array (t := i32) c.pScratchBuf (scr.take L.k6Base) ⋆ R)))) m')
            ?_ ?_
          · intro J hJ
            c0_hsteps!
            exact hJ (0#32, ks.arena) _ ⟨Nat.zero_le _, hsh.arena_len, fun _ _ => rfl,
              fun _ hj => by simp at hj, hmA⟩
          · rintro J ⟨i, ar'⟩ m' ⟨hi_le, har_len, har_old, har_new, hm'⟩ J_continue
            c0_hsplit
            · have hi_lt : i.toNat < sz.toNat := by bv_omega
              have hi_xs : i.toNat < xs.length := by omega
              have hal_i_lt : ks.alen.toNat + i.toNat < 2 ^ 32 := by omega
              have hal_i : (ks.alen + i).toNat = ks.alen.toNat + i.toNat := by
                rw [BitVec.toNat_add, Nat.mod_eq_of_lt hal_i_lt]
              have hoff_i_lt : (ks.alen + i).toNat < szAr L := by
                unfold szAr dimacsBound at *; omega
              have hi1 : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
              c0_hsteps!
              refine J_continue (i + 1#32, ar'.set (ks.alen + i).toNat (xs[i.toNat]'hi_xs)) _
                (by dsimp only; rw [hi1]; omega) ⟨by rw [hi1]; omega, by simp [har_len],
                fun j hj => by
                  rw [List.getElem?_set_ne (by rw [hal_i]; omega)]
                  exact har_old j hj,
                fun j hj => by
                  rw [hi1] at hj
                  by_cases hje : j = i.toNat
                  · subst hje
                    rw [hal_i, List.getElem?_set_self (by omega), List.getElem?_eq_getElem hi_xs]
                  · rw [List.getElem?_set_ne (by rw [hal_i]; omega)]
                    exact har_new j (by omega),
                ?_⟩
              refine Eq.mp (congrArg (fun x => (K6MemA L (L.kPtr c.pScratchBuf) x ⋆ _) _) ?_) ‹_›
              k6_ext <;> rfl
            · have hi_eq : i.toNat = sz.toNat := by bv_omega
              rw [hi_eq] at har_new
              have hnc_sz : ks.nc.toNat < szCl L := hnc_lt
              have hal1 : (ks.alen + sz).toNat = ks.alen.toNat + sz.toNat := by
                rw [BitVec.toNat_add, Nat.mod_eq_of_lt hsum_lt]
              have ⟨hinvW, hsyncW, hlvlW, hnvW, hnaW, hassW, hteW, hunW, hincW, hbdW⟩ :=
                k6AddClause_ge2_preserves hinv hsync hnc_lt hsz2 hsz_lt28 hsz_xs hoff_fit
                  har_len har_old har_new hxlits hent
              let stM := (((({ ks with arena := ar' } : K6State).putHdr .alen
                (ks.alen + sz)).putArr .clOff ks.nc.toNat ks.alen).putArr .clSz ks.nc.toNat
                  sz).putHdr .nc (ks.nc + 1#32)
              have hsh_ar : ({ ks with arena := ar' } : K6State).ShapesOk L :=
                { hsh with arena_len := har_len }
              have hshM : stM.ShapesOk L :=
                (((hsh_ar.putHdr .alen _).putArr .clOff _ _).putArr .clSz _ _).putHdr .nc _
              have hl0_lt : (xs[0]'(by omega)).toNat < 2 * L.maxV := by
                have h0 := hxlits 0 (by omega)
                rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h0
                have h0' : (xs[0]'(by omega)).toNat < 2 * ks.nv.toNat := h0
                omega
              have hl1_lt : (xs[1]'(by omega)).toNat < 2 * L.maxV := by
                have h1 := hxlits 1 (by omega)
                rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h1
                have h1' : (xs[1]'(by omega)).toNat < 2 * ks.nv.toNat := h1
                omega
              c0_hsteps_nogrp
              have hmMA : (K6MemA L (L.kPtr c.pScratchBuf) stM ⋆
                (array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
                  (array (t := i32) litsPtr xs ⋆
                    (array (t := i32) c.pScratchBuf (scr.take L.k6Base) ⋆ R)))) m := by
                refine Eq.mp (congrArg (fun x => (K6MemA L (L.kPtr c.pScratchBuf) x ⋆ _) _) ?_) ‹_›
                dsimp only [stM]; k6_ext <;> rfl
              k6_call hAddTicks
              refine ⟨L, stM, _, hshM, (k6MemA_to_mem hmMA).2, fun tk' mT hmT => ?_⟩
              · have hshT : (stM.putHdr .ticks tk').ShapesOk L := hshM.putHdr .ticks tk'
                have hmTA := k6Mem_to_amem hshT hmT
                clear hmT
                have h1_xs : 1 < xs.length := by omega
                c0_hsteps_nogrp
                have hmTA' : (K6MemA L (L.kPtr c.pScratchBuf) (stM.putHdr .ticks tk') ⋆
                  (array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
                    (array (t := i32) litsPtr xs ⋆
                      (array (t := i32) c.pScratchBuf (scr.take L.k6Base) ⋆ R)))) mT := hmTA
                k6_call hWatch
                refine ⟨L, stM.putHdr .ticks tk', _, hshT, ?_, ?_, ?_, ?_, (k6MemA_to_mem hmTA').2,
                  fun mW hmW => ?_⟩
                · dsimp only [stM]; k6_field; exact hmv_eq_ks
                · exact hnc_lt
                · exact hl0_lt
                · exact hl1_lt
                · simp only [show (BitVec.ofNat 64 1).toNat = 1 from rfl] at hmW
                  rw [k6WatchStep_putHdr_ticks stM tk' ks.nc (xs[0]'(by omega)) (xs[1]'(by omega))]
                    at hmW
                  c0_hsteps!
                  let ksW := k6WatchStep stM ks.nc (xs[0]'(by omega)) (xs[1]'(by omega))
                  have hinvWT : K6Inv L P (ksW.putHdr .ticks tk') :=
                    k6AddTicks_preserves_inv hinvW tk'
                  have hsyncWT : K6TrailSynced (ksW.putHdr .ticks tk') := hsyncW
                  have hmF := hreorg hinvWT.shapes (k6Mem_to_amem hinvWT.shapes hmW)
                  exact hQ true _ _ hmF.1 hmF.2.1 (by rw [hof_slab hinvWT.shapes]; exact hinvWT)
                    (by rw [hof_slab hinvWT.shapes]; exact hsyncWT)
                    (by rw [hof_slab hinvWT.shapes]; k6_field; exact hlvlW.trans hlvl0)
                    (by rw [hof_slab hinvWT.shapes]; k6_field; exact hnvW)
                    (by rw [hof_slab hinvWT.shapes]; k6_field; exact hnaW)
                    (by unfold k6AssumpLitsS k6AssumpLits; rw [hof_slab hinvWT.shapes]; k6_field
                        rw [hnaW, hassW])
                    (fun h => by cases h)
                    (fun _ => by
                      rw [hof_slab hinvWT.shapes]
                      refine ⟨by k6_field; rfl, by k6_field; rfl, by k6_field; exact hunW,
                        by k6_field; exact hincW⟩)
                    (fun M hxsM hM htr => by
                      rw [hof_slab hinvWT.shapes]
                      refine ⟨hbdW M hxsM hM, ?_⟩
                      change ∀ l ∈ k6TrailLits (ksW.putHdr .ticks tk'), l < 2 * M
                      have hteq : k6TrailLits (ksW.putHdr .ticks tk') = k6TrailLits ks := by
                        unfold k6TrailLits; rw [show (ksW.putHdr .ticks tk').trl_end = ks.trl_end by
                          k6_field; exact hteW]
                        dsimp only [ksW, k6WatchStep, k6WatchStep0, stM, K6State.putHdr,
                          K6State.putArr]
                      rwa [hteq]) hmF.2.2

/-! ## 3. `m8_k6_flip_wp` (`visits >> 4`) -/

private structure K6FlipStateInv (L : K6Layout) (P : (Nat → Bool) → Prop)
    (ks0 ks : K6State) (lit prev w : BitVec 32)
    (chains : List (List Nat)) (done todo : List Nat) : Prop where
  hinv : K6Inv L P ks
  hnv : ks.nv = ks0.nv
  hnass : ks.nassump = ks0.nassump
  hass : ks.assump = ks0.assump
  hneq : ks.neq = ks0.neq
  hvals : ks.vals[lit.toNat]? = some 1#32
  hlvl : ks.lvlArr[(lit >>> (1 : Nat)).toNat]?.getD 0#32 ≠ 0#32
  hcur : K6WChainCursor ks lit.toNat chains done todo prev w

private structure K6FlipBrkPost (L : K6Layout) (P : (Nat → Bool) → Prop)
    (ks0 ks : K6State) (lit : BitVec 32) (ok : Bool) : Prop where
  hinv : K6Inv L P ks
  hnv : ks.nv = ks0.nv
  hnass : ks.nassump = ks0.nassump
  hass : ks.assump = ks0.assump
  hneq : ks.neq = ks0.neq
  hok : ok = true → ks.vals[lit.toNat]? = some 1#32 ∧
    ks.lvlArr[(lit >>> (1 : Nat)).toNat]?.getD 0#32 ≠ 0#32

private theorem m8_k6_join_fullMem {c : FullCfg} {L : K6Layout} {s : FullState}
    {ks' : K6State} {R : Mem 64 → Prop} {m' : Mem 64}
    (hlen : s.LengthsOk c) (hscr_len : L.scrLen = c.scratch_cap)
    (hinv' : ks'.ShapesOk L)
    (hm' : (K6MemA L (L.kPtr c.pScratchBuf) ks' ⋆ (FullK6Frame c L s ⋆ R)) m') :
    let scr' := List.take L.k6Base s.scratch.scratch_buf ++ ks'.toSlab
    let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
    s'.LengthsOk c ∧
    (∀ i < L.k6Base, scr'[i]? = s.scratch.scratch_buf[i]?) ∧
    k6StateOfScratch L scr' = ks' ∧
    (FullMem c s' ⋆ R) m' := by
  have hscr_ok := hlen.scratch_ok.scratch_buf_len
  have hscr_klen : s.scratch.scratch_buf.length = L.scrLen := by rw [hscr_len, hscr_ok]
  have hbase_le : L.k6Base ≤ s.scratch.scratch_buf.length := by
    rw [hscr_klen]; unfold K6Layout.scrLen K6Layout.k6Base; omega
  have hslab_len : ks'.toSlab.length = L.k6Fixed + L.acap := K6State.toSlab_length hinv'
  have hscr'_len : (List.take L.k6Base s.scratch.scratch_buf ++ ks'.toSlab).length = c.scratch_cap := by
    rw [List.length_append, List.length_take, Nat.min_eq_left hbase_le, hslab_len, ← hscr_len]
    unfold K6Layout.scrLen; omega
  have hmM := (k6MemA_to_mem hm').2
  rw [← sep_assoc, sep_comm (K6Mem L (L.kPtr c.pScratchBuf) ks') (FullK6Frame c L s)] at hmM
  have hmF := fullMem_join_k6 (ks' := ks') hbase_le hinv' hmM
  refine ⟨⟨hlen.core_ok, { hlen.scratch_ok with scratch_buf_len := hscr'_len }⟩, fun i hi => ?_, ?_, hmF⟩
  · rw [List.getElem?_append_left (by rw [List.length_take, Nat.min_eq_left hbase_le]; exact hi),
      List.getElem?_take_of_lt hi]
  · unfold k6StateOfScratch
    rw [k6_slab_drop_exact (List.take L.k6Base s.scratch.scratch_buf) ks'.toSlab
      (by rw [List.length_take, Nat.min_eq_left hbase_le])]
    exact K6State.ofSlab_toSlab hinv'

/-- `full_k6_flip` `Func.wp` proof for `M8` (`visits >> 4`), matching `k6FlipSpec`. -/
theorem m8_k6_flip_wp (Γ : Env)
    (hMaxV : M6EnvSpec Γ "full_m6_max_v" m6MaxVSpec)
    (hAddTicks : M6EnvSpec Γ "full_k6_add_ticks" k6AddTicksSpec) :
    ∀ args m Q X, k6FlipSpec args m Q X → Func.wp Γ full_k6_flip_body args m Q X := by
  rintro ⟨_, lit, ⟨⟩⟩ m Q X ⟨c, s, P, L, R, rfl, hlen, hscr_len, hmaxv, hinv, hlit, hm, hQ⟩
  unfold Func.wp full_k6_flip_body
  have hscr_klen : s.scratch.scratch_buf.length = L.scrLen := by
    rw [hscr_len, hlen.scratch_ok.scratch_buf_len]
  have hscr_lt : c.scratch_cap < 2 ^ 64 := by have := c.hscr; unfold dimacsBound at this; omega
  have hmL := L.hmaxV
  have hmv_eq : (BitVec.ofNat 64 (k6MaxV c.scratch_cap)).setWidth 32 = L.mv32 := by
    apply BitVec.eq_of_toNat_eq; unfold K6Layout.mv32
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; rw [← hmaxv]; omega
  let ks := k6StateOfScratch L s.scratch.scratch_buf
  c0_hsteps_nogrp
  k6_call hMaxV
  dsimp only [m6MaxVSpec]
  rw [show (BitVec.ofNat 64 c.scratch_cap).toNat = c.scratch_cap by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hscr_lt]]
  c0_hstep; c0_hstep
  rw [hmv_eq]
  c0_hsplit
  · exfalso; unfold K6Layout.mv32 at hc; have := congrArg BitVec.toNat hc; simp at this; omega
  c0_hstep; c0_hstep; c0_hstep; c0_hstep; c0_hstep; c0_hstep; c0_hstep
  erw [k6_ptr_base_k6Base L c.pScratchBuf]
  rw [fullMem_eq_k6Frame hscr_klen, sep_comm (FullK6Frame c L s), sep_assoc] at hm
  have hm0 : (K6MemA L (L.kPtr c.pScratchBuf) ks ⋆ (FullK6Frame c L s ⋆ R)) m :=
    k6Mem_to_amem hinv.shapes hm
  clear hm
  have hlit_sz : lit.toNat < sz2V L := by unfold sz2V; have := hinv.clauses.nv_le; omega
  have hv_sz : (lit >>> (1 : Nat)).toNat < szV L := by unfold szV; have := hinv.clauses.nv_le; bv_omega
  have hm_ret_orig : ∀ {m'}, (K6MemA L (L.kPtr c.pScratchBuf) ks ⋆ (FullK6Frame c L s ⋆ R)) m' →
      Q (false, ()) m' := fun {m'} hm' => by
    obtain ⟨hlen', hpre', hks', hmF'⟩ :=
      m8_k6_join_fullMem hlen hscr_len hinv.shapes hm'
    exact hQ false _ m' hlen' hpre' (hks'.symm ▸ hinv) (by rw [hks']) (by rw [hks'])
      (by unfold k6AssumpLitsS k6AssumpLits; rw [hks']) (by rw [hks']) hmF'
  c0_hsteps_nogrp
  c0_hsplit
  · c0_hsteps!; exact hm_ret_orig ‹_›
  c0_hsplit
  · c0_hsteps!; exact hm_ret_orig ‹_›
  c0_hsteps_nogrp
  c0_hsplit
  · c0_hsteps!; exact hm_ret_orig ‹_›
  c0_hsteps_nogrp
  c0_hsplit
  · c0_hsteps!; exact hm_ret_orig ‹_›
  have hstatus0 : ks.status = 10#32 := by bv_omega
  have hvals0 : ks.vals[lit.toNat]? = some 1#32 := by
    have hlit_len : lit.toNat < ks.vals.length := by rw [hinv.shapes.vals_len]; exact hlit_sz
    have h1 : ks.vals[lit.toNat]?.getD 0#32 = 1#32 := ‹_›
    rw [List.getElem?_eq_getElem hlit_len, Option.getD_some] at h1
    rw [List.getElem?_eq_getElem hlit_len, h1]
  have hlvl0 : ks.lvlArr[(lit >>> (1 : Nat)).toNat]?.getD 0#32 ≠ 0#32 := ‹_›
  obtain ⟨chains0, hcur0⟩ :=
    K6WChainCursor.init hinv.shapes hinv.clauses.nv_le hinv.watches hlit
  have hwh_sz : lit.toNat < sz2V L := hlit_sz
  c0_hsteps_nogrp
  refine wp_while_break_state
    (brkTs := [i32, i32, i64, i64, Ty.bool])
    (lpTs := [i32, i32, i64, i64])
    (projBrk := fun st : K6State × Bool × BitVec 32 × BitVec 32 × BitVec 64 × BitVec 64 =>
      (st.2.2.1, st.2.2.2.1, st.2.2.2.2.1, st.2.2.2.2.2, st.2.1, ()))
    (fun (st, ok, _, _, _, _) m' =>
      K6FlipBrkPost L P ks st lit ok ∧ (K6MemA L (L.kPtr c.pScratchBuf) st ⋆ (FullK6Frame c L s ⋆ R)) m')
    (projLp := fun st : K6State × BitVec 32 × BitVec 32 × BitVec 64 × BitVec 64 ×
        List (List Nat) × List Nat × List Nat =>
      (st.2.1, st.2.2.1, st.2.2.2.1, st.2.2.2.2.1, ()))
    (fun st => st.2.2.2.2.2.2.2.length)
    (fun (st, w, prev, _, _, chains, done, todo) m' =>
      K6FlipStateInv L P ks st lit prev w chains done todo ∧
        (K6MemA L (L.kPtr c.pScratchBuf) st ⋆ (FullK6Frame c L s ⋆ R)) m')
    ?_ ?_ ?_
  · rintro B ⟨st, ok, w, prev, visits, ticks⟩ m' ⟨hbrk, hm'⟩
    c0_hsteps_nogrp
    k6_call hAddTicks
    refine ⟨L, st, _, hbrk.hinv.shapes, (k6MemA_to_mem hm').2, fun tk' mT hmT => ?_⟩
    have hmTA := k6Mem_to_amem (hbrk.hinv.shapes.putHdr .ticks tk') hmT
    have hinvT := k6AddTicks_preserves_inv hbrk.hinv tk'
    have hnl_sz : (lit ^^^ 1).toNat < sz2V L := by
      unfold sz2V
      have hnv_le : st.nv.toNat ≤ L.maxV := hbrk.hinv.clauses.nv_le
      have hhl : lit.toNat < 2 * st.nv.toNat := by rw [hbrk.hnv]; exact hlit
      have h1 := k6_bv32_xor1_lt hhl
      have : (lit ^^^ 1).toNat = litNeg lit.toNat := by
        simpa [show (1 : BitVec 32) = 1#32 from rfl] using h1.1
      omega
    clear hmT
    c0_hsteps_nogrp
    c0_hsplit
    · have hokt : ok = true := ‹_›
      obtain ⟨hvt, hlt⟩ := hbrk.hok hokt
      have hlit_nvT : lit.toNat < 2 * (st.putHdr .ticks tk').nv.toNat := by
        k6_field; rw [hbrk.hnv]; exact hlit
      have hinvF := k6FlipFinish_preserves hinvT hlit_nvT hvt hlt
      c0_hsteps!
      obtain ⟨hlen', hpre', hks', hmF'⟩ :=
        m8_k6_join_fullMem hlen hscr_len hinvF.shapes ‹_›
      exact hQ true _ _ hlen' hpre' (hks'.symm ▸ hinvF)
        (by rw [hks']; k6_field; exact hbrk.hnv)
        (by rw [hks']; k6_field; exact hbrk.hnass)
        (by unfold k6AssumpLitsS k6AssumpLits; rw [hks']; k6_field; rw [hbrk.hnass, hbrk.hass])
        (by rw [hks']; k6_field; exact hbrk.hneq) hmF'
    · have hokf : ok = false := by cases ok <;> simp_all
      c0_hsteps!
      obtain ⟨hlen', hpre', hks', hmF'⟩ :=
        m8_k6_join_fullMem hlen hscr_len hinvT.shapes ‹_›
      exact hQ false _ _ hlen' hpre' (hks'.symm ▸ hinvT)
        (by rw [hks']; k6_field; exact hbrk.hnv)
        (by rw [hks']; k6_field; exact hbrk.hnass)
        (by unfold k6AssumpLitsS k6AssumpLits; rw [hks']; k6_field; rw [hbrk.hnass, hbrk.hass])
        (by rw [hks']; k6_field; exact hbrk.hneq) hmF'
  · rintro B J ⟨st, w, prev, visits, ticks, chains, done, todo⟩ m' hB hJ ⟨hsf, hm'⟩
    c0_hsplit
    · have hw_ne : w ≠ 0xFFFFFFFF#32 := ‹_›
      have hlit_nv : lit.toNat < 2 * st.nv.toNat := by rw [hsf.hnv]; exact hlit
      have hshW := hsf.hinv.shapes
      have hclW := hsf.hinv.clauses
      have hac_b := L.hacap
      obtain ⟨w0, todo', hw0_wn, htodo_eq, hw_eq, hw0_nc, hw0_mc, hwnat, hcid_eq, hslot_eq,
        hsz2, har_l, hbv_nv, hbv_mem, hbin_iff, hbin_other, htail_wc⟩ :=
        hsf.hcur.step_unfold hclW.nc_le hlit_nv hw_ne
      have hw_sz : w.toNat < sz2Cl L := by unfold sz2Cl; omega
      have hcid_cl : w0 / 2 < szCl L := by unfold szCl K6Layout.maxCl at *; omega
      have hbv_sz : ((st.wblit[w.toNat]?.getD 0#32) &&& 0x7FFFFFFF#32).toNat < sz2V L := by
        unfold sz2V; have := hclW.nv_le; rw [hwnat]; omega
      c0_hsteps_nogrp
      · -- binary watch: bv = lit
        exact hB (st, false, w, prev, visits + 1#64, ticks) m'
          ⟨⟨hsf.hinv, hsf.hnv, hsf.hnass, hsf.hass, hsf.hneq, fun h => by cases h⟩, hm'⟩
      · -- binary watch: bv ≠ lit ∧ vals[bv] ≠ 1
        exact hB (st, false, w, prev, visits + 1#64, ticks) m'
          ⟨⟨hsf.hinv, hsf.hnv, hsf.hnass, hsf.hass, hsf.hneq, fun h => by cases h⟩, hm'⟩
      · -- binary watch: bv ≠ lit ∧ vals[bv] = 1
        have hcur' := k6WatchSkip_cursor hshW (hw_eq ▸ htodo_eq ▸ hsf.hcur) hw0_wn
        exact hJ (st, st.wnext[w.toNat]?.getD 0#32, w, visits + 1#64, ticks,
            chains, done ++ [w0], todo') _
          (by dsimp only; rw [htodo_eq]; simp)
          ⟨⟨hsf.hinv, hsf.hnv, hsf.hnass, hsf.hass, hsf.hneq, hsf.hvals, hsf.hlvl, by
            rw [hwnat, hw_eq]; exact hcur'⟩, hm'⟩
      · -- non-binary watch
        have hbin_z : (st.wblit[w.toNat]?.getD 0#32 &&& 0x80000000#32) = 0#32 := ‹_›
        have hsz_ne2 : k6ClauseSize st (w0 / 2) ≠ 2 := fun h2 =>
          absurd (hbin_iff.mpr h2) (by rw [← hwnat, hbin_z]; simp)
        have hwf_c := hclW.cl_wf (w0 / 2) (by omega)
        have hwc : K6WChainCursor st lit.toNat chains done (w0 :: todo') prev (BitVec.ofNat 32 w0) :=
          hw_eq ▸ htodo_eq ▸ hsf.hcur
        refine LeanQbe.T.wp_unroll_group fun Jnk hJnk => ?_
        have hnk : Jnk () m' := by
          refine hJnk () m' ?_
          have har_ok : ∀ idx < k6ClauseSize st (w0 / 2),
              k6ClauseOff st (w0 / 2) + idx < L.acap ∧
              (st.arena[k6ClauseOff st (w0 / 2) + idx]?.getD 0#32).toNat < 2 * st.nv.toNat := by
            intro idx hidx
            have hcap : k6ClauseOff st (w0 / 2) + idx < L.acap := by
              have := hclW.alen_le; omega
            have hmem : (st.arena[k6ClauseOff st (w0 / 2) + idx]?.getD 0#32).toNat ∈
                k6ClauseLits st (w0 / 2) := by
              rw [k6_mem_clauseLits_iff (by rw [hshW.arena_len]; have := hclW.alen_le; omega)]
              exact ⟨idx, hidx, rfl⟩
            exact ⟨hcap, hwf_c.2.2.1 _ hmem⟩
          have hother_slot_lt : w0 % 2 ^^^ 1 < 2 := by
            rcases Nat.mod_two_eq_zero_or_one w0 with h | h <;> simp [h]
          let other := st.arena[k6ClauseOff st (w0 / 2) + (w0 % 2 ^^^ 1)]?.getD 0#32
          have hother_nv : other.toNat < 2 * st.nv.toNat := (har_ok _ (by omega)).2
          have hot_mem : other.toNat ∈ k6ClauseLits st (w0 / 2) := by
            rw [k6_mem_clauseLits_iff (by rw [hshW.arena_len]; have := hclW.alen_le; omega)]
            exact ⟨w0 % 2 ^^^ 1, by omega, rfl⟩
          have hw_sh1 : (w >>> (1 : Nat)).toNat = w0 / 2 := hcid_eq
          have hw_m2_lt : w0 % 2 < 2 ^ 32 :=
            Nat.lt_trans (Nat.mod_lt w0 (by decide)) (by decide)
          have hm2_xor_lt : w0 % 2 ^^^ 1 < 2 ^ 32 := by
            rcases Nat.mod_two_eq_zero_or_one w0 with h | h <;> simp [h]
          have hslot_bv : (w &&& (1 : BitVec 32)) = BitVec.ofNat 32 (w0 % 2) := by
            apply BitVec.eq_of_toNat_eq
            change (w &&& 1#32).toNat = (BitVec.ofNat 32 (w0 % 2)).toNat
            rw [hslot_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw_m2_lt]
          have hslot_other_bv :
              (w &&& (1 : BitVec 32) ^^^ (1 : BitVec 32)) = BitVec.ofNat 32 (w0 % 2 ^^^ 1) := by
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_xor, show (w &&& (1 : BitVec 32)).toNat = (w &&& 1#32).toNat from rfl,
              hslot_eq, show (1 : BitVec 32).toNat = 1 from rfl, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt hm2_xor_lt]
          have hcl_off_add :
              (st.clOff[w0 / 2]?.getD 0#32 + (w &&& (1 : BitVec 32) ^^^ (1 : BitVec 32))).toNat =
              k6ClauseOff st (w0 / 2) + (w0 % 2 ^^^ 1) := by
            have hcap' : k6ClauseOff st (w0 / 2) + (w0 % 2 ^^^ 1) < L.acap :=
              (har_ok (w0 % 2 ^^^ 1) (by omega)).1
            unfold k6ClauseOff at hcap' ⊢; unfold dimacsBound at hac_b
            rw [hslot_other_bv]; have := hm2_xor_lt; bv_omega
          have hcl_off_ar :
              ((st.clOff[(w >>> (1 : Nat)).toNat]?.getD 0#32) +
                (w &&& (1 : BitVec 32) ^^^ (1 : BitVec 32))).toNat < szAr L := by
            unfold szAr; rw [hw_sh1, hcl_off_add]; exact (har_ok (w0 % 2 ^^^ 1) (by omega)).1
          have hother_mv2 : other.toNat < sz2V L := by unfold sz2V; have := hclW.nv_le; omega
          have hoth_arr_lt :
              (st.arena[(st.clOff[(w >>> (1 : Nat)).toNat]?.getD 0#32 +
                (w &&& (1 : BitVec 32) ^^^ (1 : BitVec 32))).toNat]?.getD 0#32).toNat < sz2V L := by
            rw [hw_sh1, hcl_off_add]; exact hother_mv2
          have hw_div_ar : (w >>> (1 : Nat)).toNat < szCl L := by rw [hw_sh1]; exact hcid_cl
          c0_hsteps_nogrp
          refine LeanQbe.T.wp_unroll_group fun Jsc hJsc => ?_
          have hsc : Jsc () m' := by
            refine hJsc () m' ?_
            let sz := st.clSz[w0 / 2]?.getD 0#32
            let off := st.clOff[w0 / 2]?.getD 0#32
            refine wp_while_break_state
              (projBrk := fun b : BitVec 32 × BitVec 32 × BitVec 32 => (b.1, b.2.1, b.2.2, ()))
              (fun b mb => mb = m' ∧
                (b.2.1 = 0xFFFFFFFF#32 ∨
                  (2 ≤ b.2.1.toNat ∧ b.2.1.toNat < sz.toNat ∧
                    b.2.2 = st.arena[off.toNat + b.2.1.toNat]?.getD 0#32 ∧
                    b.2.2 ≠ lit ∧ st.vals[b.2.2.toNat]? = some 1#32)))
              (projLp := fun r : BitVec 32 => (r, ())) (fun r => sz.toNat - r.toNat)
              (fun r m'' => m'' = m' ∧ r.toNat ≤ sz.toNat ∧ 2 ≤ r.toNat) ?_ ?_ ?_
            · rintro B2 ⟨_, ri, repl⟩ mb ⟨rfl, hbrk⟩
              dsimp only at hbrk ⊢
              c0_hsplit
              · c0_hsteps!
                exact hB (st, false, w, prev, visits + 1#64, ticks + 1#64) mb
                  ⟨⟨hsf.hinv, hsf.hnv, hsf.hnass, hsf.hass, hsf.hneq, fun h => by cases h⟩, hm'⟩
              · have hri_ne : ri ≠ 0xFFFFFFFF#32 := by bv_omega
                obtain ⟨hri_ge, hri_lt, hrepl_eq, hrepl_ne, _⟩ := hbrk.resolve_left hri_ne
                have hrepl_ne' : repl.toNat ≠ lit.toNat :=
                  fun h => hrepl_ne (BitVec.eq_of_toNat_eq h)
                obtain ⟨hrl_inv, ⟨chW', hwc'⟩⟩ :=
                  k6WatchReloc_preserves hsf.hinv hlit_nv hwc hri_ge hri_lt hrepl_ne' rfl hrepl_eq
                obtain ⟨hri_cap, hri_lit⟩ := har_ok ri.toNat hri_lt
                obtain ⟨hslot_cap, _⟩ :=
                  har_ok (w0 % 2) (by have := Nat.mod_lt w0 (by decide : 0 < 2); omega)
                have hslot_off_eq :
                    (st.clOff[w0 / 2]?.getD 0#32 + (w &&& (1 : BitVec 32))).toNat =
                    (st.clOff[w0 / 2]?.getD 0#32).toNat + w0 % 2 := by
                  rw [hslot_bv]; unfold dimacsBound at hac_b
                  change (st.clOff[w0 / 2]?.getD 0#32 + BitVec.ofNat 32 (w0 % 2)).toNat = _
                  change k6ClauseOff st (w0 / 2) + w0 % 2 < L.acap at hslot_cap
                  unfold k6ClauseOff at hslot_cap; bv_omega
                have hslot_ar :
                    (st.clOff[(w >>> (1 : Nat)).toNat]?.getD 0#32 +
                      (w &&& (1 : BitVec 32))).toNat < szAr L := by
                  unfold szAr; rw [hw_sh1, hslot_off_eq]; exact hslot_cap
                have hri_off_eq :
                    (st.clOff[w0 / 2]?.getD 0#32 + ri).toNat =
                    (st.clOff[w0 / 2]?.getD 0#32).toNat + ri.toNat := by
                  unfold dimacsBound at hac_b
                  change k6ClauseOff st (w0 / 2) + ri.toNat < L.acap at hri_cap
                  unfold k6ClauseOff at hri_cap; bv_omega
                have hri_ar :
                    (st.clOff[(w >>> (1 : Nat)).toNat]?.getD 0#32 + ri).toNat < szAr L := by
                  unfold szAr; rw [hw_sh1, hri_off_eq]; exact hri_cap
                have hrepl_mv2 : repl.toNat < sz2V L := by
                  change repl = st.arena[k6ClauseOff st (w0 / 2) + ri.toNat]?.getD 0#32 at hrepl_eq
                  rw [hrepl_eq]; unfold sz2V; have := hclW.nv_le; omega
                have hlit_bn : BitVec.ofNat 32 lit.toNat = lit := by simp
                have hprv_lt : prev ≠ 0xFFFFFFFF#32 → prev.toNat < sz2Cl L := fun hp => by
                  rcases hwc.prev_rel with ⟨_, hpf, _⟩ | ⟨_, u, _, hp_eq, hu_len, _⟩
                  · exact absurd hpf hp
                  · rw [hshW.wnext_len] at hu_len
                    have hu32 : u < 2 ^ 32 := by unfold K6Layout.maxCl at hu_len; omega
                    rw [hp_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hu32]
                    unfold sz2Cl; exact hu_len
                c0_hsteps_nogrp
                try refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
                c0_hsplit
                · have hpeq : prev = 0xFFFFFFFF#32 := by bv_omega
                  c0_hsteps!
                  refine hJ (_, st.wnext[w.toNat]?.getD 0#32, prev, visits + 1#64, ticks + 1#64,
                      chW', done, todo') _ (by dsimp only; rw [htodo_eq]; simp)
                    ⟨⟨hrl_inv, by dsimp only [k6WatchStep0]; exact hsf.hnv,
                      by dsimp only [k6WatchStep0]; exact hsf.hnass,
                      by dsimp only [k6WatchStep0]; exact hsf.hass,
                      by dsimp only [k6WatchStep0]; exact hsf.hneq,
                      by dsimp only [k6WatchStep0]; exact hsf.hvals,
                      by dsimp only [k6WatchStep0]; exact hsf.hlvl,
                      by rw [hwnat]; exact hwc'⟩, ?_⟩
                  refine Eq.mp (congrArg (fun x => (K6MemA L (L.kPtr c.pScratchBuf) x ⋆ _) _) ?_) ‹_›
                  dsimp only [k6WatchStep0, k6ClauseOff]; simp only [hpeq, ↓reduceIte]
                  k6_ext <;> (first | rfl | {
                    try rw [hwnat]
                    try rw [hw_sh1]
                    try rw [hcl_off_add]
                    try rw [hslot_off_eq]
                    try rw [hri_off_eq]
                    try rw [hlit_bn]
                    try rw [hw_eq]
                    try rw [show (BitVec.ofNat 32 w0).toNat = w0 from hw_eq ▸ hwnat]
                    try dsimp only [k6ClauseOff]
                    try rfl })
                · have hpne : prev ≠ 0xFFFFFFFF#32 := by bv_omega
                  have hprv_bd := hprv_lt hpne
                  c0_hsteps!
                  refine hJ (_, st.wnext[w.toNat]?.getD 0#32, prev, visits + 1#64, ticks + 1#64,
                      chW', done, todo') _ (by dsimp only; rw [htodo_eq]; simp)
                    ⟨⟨hrl_inv, by dsimp only [k6WatchStep0]; exact hsf.hnv,
                      by dsimp only [k6WatchStep0]; exact hsf.hnass,
                      by dsimp only [k6WatchStep0]; exact hsf.hass,
                      by dsimp only [k6WatchStep0]; exact hsf.hneq,
                      by dsimp only [k6WatchStep0]; exact hsf.hvals,
                      by dsimp only [k6WatchStep0]; exact hsf.hlvl,
                      by rw [hwnat]; exact hwc'⟩, ?_⟩
                  refine Eq.mp (congrArg (fun x => (K6MemA L (L.kPtr c.pScratchBuf) x ⋆ _) _) ?_) ‹_›
                  dsimp only [k6WatchStep0, k6ClauseOff]; simp only [hpne, ↓reduceIte]
                  k6_ext <;> (first | rfl | {
                    try rw [hwnat]
                    try rw [hw_sh1]
                    try rw [hcl_off_add]
                    try rw [hslot_off_eq]
                    try rw [hri_off_eq]
                    try rw [hlit_bn]
                    try rw [hw_eq]
                    try rw [show (BitVec.ofNat 32 w0).toNat = w0 from hw_eq ▸ hwnat]
                    try dsimp only [k6ClauseOff]
                    try rfl })
            · intro B2 L2 r m1 hB2 ih1 ⟨rfl, hr_le, hr2⟩
              dsimp only at hr_le hr2 ⊢
              c0_hsplit
              · have hr_lt : r.toNat < sz.toNat := by
                  have hc0 : r.toNat < (st.clSz[w.toNat / 2]?.getD 0#32).toNat := by
                    bv_omega
                  simpa only [sz, hwnat] using hc0
                obtain ⟨hr_cap, hr_lit⟩ := har_ok r.toNat hr_lt
                have hr_ar : (st.clOff[(w >>> (1 : Nat)).toNat]?.getD 0#32 + r).toNat < szAr L := by
                  rw [hw_sh1]; unfold szAr dimacsBound at *
                  change k6ClauseOff st (w0 / 2) + r.toNat < L.acap at hr_cap
                  unfold k6ClauseOff at hr_cap; bv_omega
                have hcand_mv2 :
                    (st.arena[(st.clOff[(w >>> (1 : Nat)).toNat]?.getD 0#32 + r).toNat]?.getD
                      0#32).toNat < sz2V L := by
                  rw [hw_sh1]
                  have hco : (st.clOff[w0 / 2]?.getD 0#32 + r).toNat =
                      k6ClauseOff st (w0 / 2) + r.toNat := by
                    unfold k6ClauseOff at hr_cap ⊢; unfold dimacsBound at hac_b; bv_omega
                  rw [hco]; unfold sz2V; have := hclW.nv_le; omega
                have hr1_wrap : (r + 1#32).toNat = r.toNat + 1 := by
                  have hsz_bd : sz.toNat < 2 ^ 28 := by
                    have := hclW.alen_le; unfold dimacsBound at hac_b
                    change k6ClauseSize st (w0 / 2) < 2 ^ 28; omega
                  bv_omega
                c0_hsteps_nogrp
                refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
                c0_hsplit
                · have hne_cand : st.arena[off.toNat + r.toNat]?.getD 0#32 ≠ lit := by
                    have hco : (st.clOff[(w >>> (1 : Nat)).toNat]?.getD 0#32 + r).toNat =
                        off.toNat + r.toNat := by
                      rw [hw_sh1]; change (off + r).toNat = off.toNat + r.toNat; unfold off
                      have hcap' : k6ClauseOff st (w0 / 2) + r.toNat < L.acap := hr_cap
                      unfold k6ClauseOff at hcap'; unfold dimacsBound at hac_b; bv_omega
                    have hc0 : st.arena[(st.clOff[(w >>> (1 : Nat)).toNat]?.getD 0#32 +
                        r).toNat]?.getD 0#32 ≠ lit := ‹_›
                    rwa [hco] at hc0
                  c0_hsplit
                  · have hc_val1 :
                        st.vals[(st.arena[off.toNat + r.toNat]?.getD 0#32).toNat]? = some 1#32 := by
                      have hvl : (st.arena[off.toNat + r.toNat]?.getD 0#32).toNat <
                          st.vals.length := by
                        rw [hshW.vals_len]
                        change (st.arena[k6ClauseOff st (w0 / 2) + r.toNat]?.getD 0#32).toNat <
                          2 * L.maxV
                        have := hclW.nv_le; omega
                      have hco : (st.clOff[(w >>> (1 : Nat)).toNat]?.getD 0#32 + r).toNat =
                          off.toNat + r.toNat := by
                        rw [hw_sh1]; change (off + r).toNat = off.toNat + r.toNat; unfold off
                        change k6ClauseOff st (w0 / 2) + r.toNat < L.acap at hr_cap
                        unfold k6ClauseOff at hr_cap; unfold dimacsBound at hac_b; bv_omega
                      have hc0 :
                          st.vals[(st.arena[(st.clOff[(w >>> (1 : Nat)).toNat]?.getD 0#32 +
                            r).toNat]?.getD 0#32).toNat]?.getD 0#32 = 1#32 := ‹_›
                      rw [hco] at hc0
                      rw [List.getElem?_eq_getElem hvl, Option.getD_some] at hc0
                      rw [List.getElem?_eq_getElem hvl, hc0]
                    c0_hsteps!
                    have hco : (st.clOff[(w >>> (1 : Nat)).toNat]?.getD 0#32 + r).toNat =
                        off.toNat + r.toNat := by
                      rw [hw_sh1]; change (off + r).toNat = off.toNat + r.toNat; unfold off
                      change k6ClauseOff st (w0 / 2) + r.toNat < L.acap at hr_cap
                      unfold k6ClauseOff at hr_cap; unfold dimacsBound at hac_b; bv_omega
                    rw [hco]
                    exact hB2 (r, r, st.arena[off.toNat + r.toNat]?.getD 0#32) _
                      ⟨rfl, Or.inr ⟨hr2, hr_lt, rfl, hne_cand, hc_val1⟩⟩
                  · c0_hsteps!
                    exact ih1 (r + 1#32) _ (by rw [hr1_wrap]; omega)
                      ⟨rfl, by rw [hr1_wrap]; omega, by rw [hr1_wrap]; omega⟩
                · c0_hsteps!
                  exact ih1 (r + 1#32) _ (by rw [hr1_wrap]; omega)
                    ⟨rfl, by rw [hr1_wrap]; omega, by rw [hr1_wrap]; omega⟩
              · c0_hsteps!; exact hB2 (r, 0xFFFFFFFF#32, 0#32) _ ⟨rfl, Or.inl rfl⟩
            · intro B2 L2 _ hL2; c0_hsteps!; exact hL2 2#32 m' ⟨rfl, hsz2, le_refl _⟩
          c0_hsplit
          · c0_hsplit
            · obtain ⟨hkp_inv, hkp_wc⟩ :=
                k6WatchKeep_preserves hsf.hinv hlit_nv hwc hother_nv hot_mem hsz_ne2
              c0_hsteps!
              refine hJ (st.putArr .wblit w0 other, st.wnext[w.toNat]?.getD 0#32, w,
                  visits + 1#64, ticks + 1#64, chains, done ++ [w0], todo') _
                (by dsimp only; rw [htodo_eq]; simp)
                ⟨⟨hkp_inv, by k6_field; exact hsf.hnv, by k6_field; exact hsf.hnass,
                  by k6_field; exact hsf.hass, by k6_field; exact hsf.hneq,
                  by k6_field; exact hsf.hvals, by k6_field; exact hsf.hlvl,
                  by rw [hwnat, hw_eq]; exact hkp_wc⟩, ?_⟩
              refine Eq.mp (congrArg (fun x => (K6MemA L (L.kPtr c.pScratchBuf) x ⋆ _) _) ?_) ‹_›
              k6_ext <;> (first | rfl | {
                dsimp only [other]
                try rw [hwnat]
                try rw [hw_sh1]
                try rw [hcl_off_add]
                try dsimp only [k6ClauseOff]
                try rfl })
            · exact head_wp_jump rfl rfl hsc
          · exact head_wp_jump rfl rfl hsc
        c0_hsplit
        · c0_hsplit
          · have hskip := k6WatchSkip_cursor hshW hwc hw0_wn
            c0_hsteps!
            exact hJ (st, st.wnext[w.toNat]?.getD 0#32, w, visits + 1#64, ticks,
                chains, done ++ [w0], todo') _
              (by dsimp only; rw [htodo_eq]; simp)
              ⟨⟨hsf.hinv, hsf.hnv, hsf.hnass, hsf.hass, hsf.hneq, hsf.hvals, hsf.hlvl, by
                rw [hwnat, hw_eq]; exact hskip⟩, hm'⟩
          · exact head_wp_jump rfl rfl hnk
        · exact head_wp_jump rfl rfl hnk
    · c0_hsteps!
      exact hB (st, true, w, prev, visits, ticks) m'
        ⟨⟨hsf.hinv, hsf.hnv, hsf.hnass, hsf.hass, hsf.hneq, fun _ => ⟨hsf.hvals, hsf.hlvl⟩⟩, hm'⟩
  · intro B J hB hJ
    c0_hsteps!
    exact hJ (ks, ks.whead[lit.toNat]?.getD 0#32, 0xFFFFFFFF#32, 0#64, 1#64,
        chains0, [], chains0[lit.toNat]?.getD []) m
      ⟨⟨hinv, rfl, rfl, rfl, rfl, hvals0, hlvl0, hcur0⟩, hm0⟩

/-! ## 4. `m8_k6_propagate_wp` (`visits >> 4`, early `ticks += 1ULL`) -/

private structure K6PropFrame (L : K6Layout) (c : (Nat → Bool) → Prop) (ks0 ks : K6State) : Prop where
  hinv : K6Inv L c ks
  hsync : K6TrailSynced ks
  hpres : K6PropPreserved ks0 ks
  htrl_ge : ks0.trl_end.toNat ≤ ks.trl_end.toNat
  hold : ∀ i < ks0.trl_end.toNat,
    ks.trl[i]? = ks0.trl[i]? ∧
    ks.lvlArr[(ks0.trl[i]?.getD 0#32).toNat / 2]? = ks0.lvlArr[(ks0.trl[i]?.getD 0#32).toNat / 2]? ∧
    ks.rsn[(ks0.trl[i]?.getD 0#32).toNat / 2]? = ks0.rsn[(ks0.trl[i]?.getD 0#32).toNat / 2]?
  hnew : ∀ i, ks0.trl_end.toNat ≤ i → i < ks.trl_end.toNat →
    ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 = ks0.lvl ∧
    ks.rsn[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 ≠ 0xFFFFFFFF#32

private theorem m8_k6PropPreserved_refl (ks : K6State) : K6PropPreserved ks ks :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem m8_k6PropFrame_refl {L : K6Layout} {c : (Nat → Bool) → Prop} {ks : K6State}
    (hinv : K6Inv L c ks) (hsync : K6TrailSynced ks) : K6PropFrame L c ks ks :=
  ⟨hinv, hsync, m8_k6PropPreserved_refl ks, le_refl _, fun _ _ => ⟨rfl, rfl, rfl⟩,
    fun _ h1 h2 => by omega⟩

private theorem m8_k6WatchesOk_putHdr {ks : K6State} (hw : K6WatchesOk ks) (f : K6HdrField)
    (hf : f = .prop ∨ f = .ticks) (v : BitVec 32) : K6WatchesOk (ks.putHdr f v) := by
  rcases hf with rfl | rfl <;> exact hw

private theorem m8_k6ReasonOk_putHdr {ks : K6State} (hr : K6ReasonOk ks) (f : K6HdrField)
    (hf : f = .prop ∨ f = .ticks) (v : BitVec 32) : K6ReasonOk (ks.putHdr f v) := by
  rcases hf with rfl | rfl <;> exact hr

private theorem m8_k6TrailSynced_putHdr {ks : K6State} (hs : K6TrailSynced ks) (f : K6HdrField)
    (hf : f = .prop ∨ f = .ticks) (v : BitVec 32) : K6TrailSynced (ks.putHdr f v) := by
  rcases hf with rfl | rfl <;> simpa [K6TrailSynced, K6State.putHdr] using hs

private theorem m8_k6BumpProp_frame {L : K6Layout} {c : (Nat → Bool) → Prop} {ks0 ks : K6State}
    (hf : K6PropFrame L c ks0 ks) (hlt : ks.prop.toNat < ks.trl_end.toNat) :
    K6PropFrame L c ks0 (ks.putHdr .prop (ks.prop + 1#32)) := by
  have hnv_le := hf.hinv.clauses.nv_le
  have hte_le := hf.hinv.assign.trl_end_le
  have hmV := L.hmaxV
  have hp1 : (ks.prop + 1#32).toNat = ks.prop.toNat + 1 := by bv_omega
  have hcl' : K6ClausesOk L c (ks.putHdr .prop (ks.prop + 1#32)) :=
    { hf.hinv.clauses with }
  have hass' : K6BaseAssignOk c (ks.putHdr .prop (ks.prop + 1#32)) :=
    { hf.hinv.assign with prop_le := by change (ks.prop + 1#32).toNat ≤ ks.trl_end.toNat; omega }
  have hinv' : K6Inv L c (ks.putHdr .prop (ks.prop + 1#32)) :=
    ⟨hf.hinv.shapes.putHdr .prop _, hcl', m8_k6WatchesOk_putHdr hf.hinv.watches .prop (Or.inl rfl) _,
      hass', m8_k6ReasonOk_putHdr hf.hinv.reasons .prop (Or.inl rfl) _⟩
  exact ⟨hinv', m8_k6TrailSynced_putHdr hf.hsync .prop (Or.inl rfl) _,
    { hf.hpres with }, hf.htrl_ge, hf.hold, hf.hnew⟩

private theorem m8_k6PropFrame_ticks {L : K6Layout} {c : (Nat → Bool) → Prop} {ks0 ks : K6State}
    (hf : K6PropFrame L c ks0 ks) (tk' : BitVec 32) :
    K6PropFrame L c ks0 (ks.putHdr .ticks tk') :=
  ⟨k6AddTicks_preserves_inv hf.hinv tk', m8_k6TrailSynced_putHdr hf.hsync .ticks (Or.inr rfl) _,
    { hf.hpres with }, hf.htrl_ge, hf.hold, hf.hnew⟩

private theorem m8_k6WChainCursor_assignStep {ks : K6State} {l : Nat} {chains : List (List Nat)}
    {done todo : List Nat} {prev w : BitVec 32} (hcur : K6WChainCursor ks l chains done todo prev w)
    (lit rsn : BitVec 32) :
    K6WChainCursor (k6AssignStep ks lit rsn) l chains done todo prev w := by
  exact
    { len_eq := hcur.len_eq
      nodup := hcur.nodup
      chain_l := hcur.chain_l
      chains_wc := hcur.chains_wc
      chains_bnd := hcur.chains_bnd
      tail_wc := hcur.tail_wc
      prev_rel := hcur.prev_rel }

private theorem m8_k6AssignStep_propFrame {L : K6Layout} {c : (Nat → Bool) → Prop} {ks0 ks : K6State}
    (hf : K6PropFrame L c ks0 ks) {lit : BitVec 32} {cid : Nat}
    (hlit : lit.toNat < 2 * ks.nv.toNat) (hzero : ks.vals[lit.toNat]? = some 0#32)
    (hcid_lt : cid < ks.nc.toNat) (hmem : lit.toNat ∈ k6ClauseLits ks cid)
    (hoth : ∀ x ∈ k6ClauseLits ks cid, x ≠ lit.toNat → ks.vals[x]? = some 2#32) :
    let cid32 := BitVec.ofNat 32 cid
    K6PropFrame L c ks0 (k6AssignStep ks lit cid32) := by
  intro cid32
  have hmV := L.hmaxV
  have hnv_le := hf.hinv.clauses.nv_le
  have hnc_le := hf.hinv.clauses.nc_le
  have hcid32_ne : cid32 ≠ 0xFFFFFFFF#32 := by
    intro h; have h1 := congrArg BitVec.toNat h
    unfold K6Layout.maxCl at hnc_le; have hac := L.hacap; unfold dimacsBound at hac
    simp only [cid32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : cid < 2 ^ 32)] at h1
    change cid = 4294967295 at h1; omega
  have hcid32_toNat : cid32.toNat = cid := by
    unfold K6Layout.maxCl at hnc_le; have hac := L.hacap; unfold dimacsBound at hac
    simp [cid32, Nat.mod_eq_of_lt (by omega : cid < 2 ^ 32)]
  have hoth_trl : ∀ x ∈ k6ClauseLits ks cid32.toNat, x ≠ lit.toNat →
      ∃ j < ks.trl_end.toNat, (ks.trl[j]?.getD 0#32).toNat = x ^^^ 1 := by
    rw [hcid32_toNat]; intro x hx hne
    have hwf := hf.hinv.clauses.cl_wf cid hcid_lt
    exact k6_falsified_to_trail hf.hinv.assign hf.hsync (hwf.2.2.1 x hx) (hoth x hx hne)
  have hent0 : ks.lvl = 0#32 → FullM4Sweep.SemEntails c [lit.toNat] := by
    intro hlvl0 β hP
    have hwf := hf.hinv.clauses.cl_wf cid hcid_lt
    obtain ⟨x, hx, hxt⟩ := (clause_sat_cnfClause_iff β (k6ClauseLits ks cid)).mp (hwf.2.2.2 β hP)
    by_cases hxl : x = lit.toNat
    · subst hxl; exact (sat_cnfClause_singleton β lit.toNat).mpr hxt
    · obtain ⟨_, hentx⟩ := k6_falsified_lvl0_entails hf.hinv hlvl0 (hwf.2.2.1 x hx) (hoth x hx hxl)
      have hneg : (cnfClause [litNeg x]).Sat β := hentx β hP
      rw [sat_cnfClause_litNeg_iff] at hneg
      exact absurd ((sat_cnfClause_singleton β x).mpr hxt) hneg
  have ⟨hinv', hsync'⟩ := k6AssignStep_preserves_inv hf.hinv hf.hsync hlit hzero hent0
    (fun _ hne => absurd hne hcid32_ne)
    (Or.inr ⟨by rw [hcid32_toNat]; exact hcid_lt, by rw [hcid32_toNat]; exact hmem, hoth_trl⟩)
  have hte_lt : ks.trl_end.toNat < ks.nv.toNat :=
    k6_trl_end_lt_of_unassigned hf.hinv.shapes hnv_le hf.hinv.assign hlit (by rw [hzero]; rfl)
  have hte1 : (ks.trl_end + 1#32).toNat = ks.trl_end.toNat + 1 := by bv_omega
  have hnot_on_trl : ∀ i < ks.trl_end.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 ≠ (lit >>> (1 : Nat)).toNat := by
    intro i hi heq
    have hshr : (lit >>> (1 : Nat)).toNat = lit.toNat / 2 := by
      simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    rw [hshr] at heq
    have hnz := (hf.hinv.assign.vals_nz_iff_trl lit.toNat hlit).mpr ⟨i, hi, heq⟩
    apply hnz; rw [hzero]; rfl
  have hlvl_lt : (lit >>> (1 : Nat)).toNat < ks.lvlArr.length := by
    rw [hf.hinv.shapes.lvlArr_len]
    have hshr : (lit >>> (1 : Nat)).toNat = lit.toNat / 2 := by
      simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    omega
  have hrsn_lt : (lit >>> (1 : Nat)).toNat < ks.rsn.length := by
    rw [hf.hinv.shapes.rsn_len]
    have hshr : (lit >>> (1 : Nat)).toNat = lit.toNat / 2 := by
      simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    omega
  have htrl_lt : ks.trl_end.toNat < ks.trl.length := by
    rw [hf.hinv.shapes.trl_len]; omega
  refine ⟨hinv', hsync', ?_,
    by rw [show (k6AssignStep ks lit cid32).trl_end.toNat = (ks.trl_end + 1#32).toNat from rfl, hte1]
       have := hf.htrl_ge; omega,
    ?_, ?_⟩
  · exact ⟨hf.hpres.nv, hf.hpres.nc, hf.hpres.lvl, hf.hpres.incons, hf.hpres.alen, hf.hpres.acap,
      hf.hpres.nassump, hf.hpres.status, hf.hpres.openCnt, hf.hpres.max_v, hf.hpres.max_orig,
      hf.hpres.max_cl, hf.hpres.neq, hf.hpres.assump⟩
  · intro i hi
    have hi_ks : i < ks.trl_end.toNat := Nat.lt_of_lt_of_le hi hf.htrl_ge
    obtain ⟨h1, h2, h3⟩ := hf.hold i hi
    have hne_i : ks.trl_end.toNat ≠ i := Nat.ne_of_gt hi_ks
    have htr_i : (ks.trl[i]?.getD 0#32).toNat / 2 = (ks0.trl[i]?.getD 0#32).toNat / 2 := by
      have hx : ks.trl[i]? = ks0.trl[i]? := h1
      simp only [hx]
    have hne_v : (ks0.trl[i]?.getD 0#32).toNat / 2 ≠ (lit >>> (1 : Nat)).toNat := by
      rw [← htr_i]; exact hnot_on_trl i hi_ks
    refine ⟨?_, ?_, ?_⟩
    · dsimp only [k6AssignStep]; rw [List.getElem?_set_ne hne_i]; exact h1
    · dsimp only [k6AssignStep]; rw [List.getElem?_set_ne hne_v.symm]; exact h2
    · dsimp only [k6AssignStep]; rw [List.getElem?_set_ne hne_v.symm]; exact h3
  · intro i hi1 hi2
    change i < (ks.trl_end + 1#32).toNat at hi2; rw [hte1] at hi2
    by_cases hilt : i < ks.trl_end.toNat
    · obtain ⟨h1, h2⟩ := hf.hnew i hi1 hilt
      have hne_i : ks.trl_end.toNat ≠ i := Nat.ne_of_gt hilt
      have hne_v : (ks.trl[i]?.getD 0#32).toNat / 2 ≠ (lit >>> (1 : Nat)).toNat := hnot_on_trl i hilt
      dsimp only [k6AssignStep]
      rw [List.getElem?_set_ne hne_i, List.getElem?_set_ne hne_v.symm, List.getElem?_set_ne hne_v.symm]
      exact ⟨h1, h2⟩
    · have hieq : i = ks.trl_end.toNat := by omega
      subst hieq
      dsimp only [k6AssignStep]
      rw [List.getElem?_set_self htrl_lt, Option.getD_some]
      have hdiv : lit.toNat / 2 = (lit >>> (1 : Nat)).toNat := by
        simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      rw [hdiv, List.getElem?_set_self hlvl_lt, List.getElem?_set_self hrsn_lt]
      simp only [Option.getD_some]
      exact ⟨hf.hpres.lvl, hcid32_ne⟩

private theorem m8_k6PropFrame_watchStep {L : K6Layout} {c : (Nat → Bool) → Prop} {ks0 ks ks' : K6State}
    (hf : K6PropFrame L c ks0 ks) (hinv' : K6Inv L c ks')
    (hnv : ks'.nv = ks.nv) (hnc : ks'.nc = ks.nc) (hlvl : ks'.lvl = ks.lvl)
    (hincons : ks'.incons = ks.incons) (halen : ks'.alen = ks.alen) (hacap : ks'.acap = ks.acap)
    (hnass : ks'.nassump = ks.nassump) (hst : ks'.status = ks.status) (hoc : ks'.openCnt = ks.openCnt)
    (hmv : ks'.max_v = ks.max_v) (hmo : ks'.max_orig = ks.max_orig) (hmc : ks'.max_cl = ks.max_cl)
    (hneq : ks'.neq = ks.neq) (hass : ks'.assump = ks.assump)
    (hte : ks'.trl_end = ks.trl_end) (htrl : ks'.trl = ks.trl)
    (hla : ks'.lvlArr = ks.lvlArr) (hrsn : ks'.rsn = ks.rsn) (hvals : ks'.vals = ks.vals) :
    K6PropFrame L c ks0 ks' := by
  refine ⟨hinv', ?_, ?_, hte ▸ hf.htrl_ge, ?_, ?_⟩
  · simpa [K6TrailSynced, hte, htrl, hvals] using hf.hsync
  · exact ⟨hnv.trans hf.hpres.nv, hnc.trans hf.hpres.nc, hlvl.trans hf.hpres.lvl,
      hincons.trans hf.hpres.incons, halen.trans hf.hpres.alen, hacap.trans hf.hpres.acap,
      hnass.trans hf.hpres.nassump, hst.trans hf.hpres.status, hoc.trans hf.hpres.openCnt,
      hmv.trans hf.hpres.max_v, hmo.trans hf.hpres.max_orig, hmc.trans hf.hpres.max_cl,
      hneq.trans hf.hpres.neq, hass.trans hf.hpres.assump⟩
  · intro i hi; simp only [htrl, hla, hrsn]; exact hf.hold i hi
  · intro i hi1 hi2; simp only [hte, htrl, hla, hrsn] at hi2 ⊢; exact hf.hnew i hi1 hi2

/-- `full_k6_propagate` `Func.wp` proof for `M8` (`visits >> 4` and early `ticks += 1ULL`),
matching `k6PropagateSpec`. -/
theorem m8_k6_propagate_wp (Γ : Env)
    (hAddTicks : M6EnvSpec Γ "full_k6_add_ticks" k6AddTicksSpec)
    (hAssign : M6EnvSpec Γ "full_k6_assign" k6AssignSpec) :
    ∀ args m Q X, k6PropagateSpec args m Q X → Func.wp Γ full_k6_propagate_body args m Q X := by
  rintro ⟨kp, ⟨⟩⟩ m Q X ⟨L, c, ks, P, hinv, hsync, hm, hQ⟩
  unfold Func.wp full_k6_propagate_body
  have hmA := k6Mem_to_amem hinv.shapes hm
  have hmv_eq : ks.max_v = L.mv32 := hinv.clauses.max_v_eq
  c0_hsteps_nogrp
  rw [hmv_eq]
  refine wp_while_state (ts := [i64]) (proj := fun st : K6State × BitVec 64 => (st.2, ()))
    (fun st => ks.nv.toNat - st.1.prop.toNat)
    (fun (st, _) m' => K6PropFrame L c ks st ∧ (K6MemA L kp st ⋆ P) m') ?_ ?_
  · intro J hJ; c0_hsteps!; exact hJ (ks, 0#64) m ⟨m8_k6PropFrame_refl hinv hsync, hmA⟩
  · intro J ⟨st, ticks⟩ m' ⟨hf_st, hm'⟩ hJ
    have hsh0 := hf_st.hinv.shapes
    have hcl0 := hf_st.hinv.clauses
    c0_hsplit
    · have hlt : st.prop.toNat < st.trl_end.toNat := by bv_omega
      have hpr_lt_nv : st.prop.toNat < st.nv.toNat := Nat.lt_of_lt_of_le hlt hf_st.hinv.assign.trl_end_le
      have hpr_szV : st.prop.toNat < szV L := by unfold szV; have := hcl0.nv_le; omega
      have htr_mem : (st.trl[st.prop.toNat]?.getD 0#32).toNat ∈ k6TrailLits st := by
        unfold k6TrailLits; rw [List.mem_map]; refine ⟨st.trl[st.prop.toNat]?.getD 0#32, ?_, rfl⟩
        have htl := hsh0.trl_len; have hnl := hcl0.nv_le
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
        exact List.mem_iff_getElem.mpr ⟨st.prop.toNat, by simp only [List.length_take]; omega, by simp⟩
      have hlit_nv : (st.trl[st.prop.toNat]?.getD 0#32).toNat < 2 * st.nv.toNat :=
        hf_st.hinv.assign.trl_lt _ htr_mem
      let lit0 := st.trl[st.prop.toNat]?.getD 0#32
      have hnl_pair := k6_bv32_xor1_lt (l := lit0) hlit_nv
      have hnl_sz : (lit0 ^^^ 1#32).toNat < sz2V L := by
        unfold sz2V; have := hcl0.nv_le; exact Nat.lt_of_lt_of_le hnl_pair.2 (by omega)
      have hnl_fal0 : st.vals[(lit0 ^^^ 1#32).toNat]? = some 2#32 := by
        have hs := hf_st.hsync st.prop.toNat hlt
        simpa [lit0, hnl_pair.1, litNeg] using hs.2
      have hpr1_wrap : (st.prop + 1#32).toNat = st.prop.toNat + 1 := by
        have := hcl0.nv_le; have := L.hmaxV; bv_omega
      have hf_bump := m8_k6BumpProp_frame hf_st hlt
      c0_hsteps_nogrp
      refine wp_while_state (ts := [i64, i64, i32, i32])
        (proj := fun stw : K6State × BitVec 32 × BitVec 64 × BitVec 64 × BitVec 32 × BitVec 32 ×
            List (List Nat) × List Nat × List Nat =>
          (stw.2.2.1, stw.2.2.2.1, stw.2.2.2.2.1, stw.2.2.2.2.2.1, ()))
        (fun stw => stw.2.2.2.2.2.2.2.2.length)
        (fun (stw, nl, _, _, prev, w, chains, done, todo) mw =>
          K6PropFrame L c ks stw ∧ nl = lit0 ^^^ 1#32 ∧ stw.prop = st.prop + 1#32 ∧
            nl.toNat < 2 * stw.nv.toNat ∧ stw.vals[nl.toNat]? = some 2#32 ∧
            K6WChainCursor stw nl.toNat chains done todo prev w ∧
            (K6MemA L kp stw ⋆ P) mw) ?_ ?_
      · intro Jw hJw
        obtain ⟨chains0, hcur0⟩ :=
          K6WChainCursor.init hf_bump.hinv.shapes hf_bump.hinv.clauses.nv_le hf_bump.hinv.watches
            (l := (lit0 ^^^ 1#32).toNat) hnl_pair.2
        c0_hsteps!
        exact hJw (st.putHdr .prop (st.prop + 1#32), lit0 ^^^ 1#32, ticks, 0#64, 0xFFFFFFFF#32,
            (st.putHdr .prop (st.prop + 1#32)).whead[(lit0 ^^^ 1#32).toNat]?.getD 0#32,
            chains0, [], chains0[(lit0 ^^^ 1#32).toNat]?.getD []) _
          ⟨hf_bump, rfl, rfl, hnl_pair.2, hnl_fal0, hcur0, ‹_›⟩
      · intro Jw ⟨stw, nl, ticks', visits, prev, w, chains, done, todo⟩ mw
            ⟨hfw, hnl_lit, hpr_w, hnlW, hnl_fal, hcurW, hmw⟩ hJw
        have hshW := hfw.hinv.shapes
        have hclW := hfw.hinv.clauses
        have hac_b := L.hacap
        have ret_confl : ∀ (cid32 : BitVec 32) (tk : BitVec 64) (mw' : Mem 64),
            (K6MemA L kp stw ⋆ P) mw' →
            cid32 ≠ 0xFFFFFFFF#32 →
            cid32.toNat < stw.nc.toNat →
            (∀ l ∈ k6ClauseLits stw cid32.toNat, stw.vals[l]? = some 2#32) →
            wp Γ Q X
              (Expr.call (as := [i64, i64]) (bs := []) "full_k6_add_ticks" (Arg.var kp, Arg.var tk, ()) fun _ =>
                Expr.ret (Arg.var cid32, ())) mw' := by
          intro cid32 tk mw' hm' hc_ne hc_lt hfal
          k6_call hAddTicks
          refine ⟨L, stw, _, hshW, (k6MemA_to_mem hm').2, fun tk' mT hmT => ?_⟩
          have hfT := m8_k6PropFrame_ticks hfw tk'
          c0_hsteps!
          exact hQ cid32 _ mT hfT.hinv hfT.hsync hfT.hpres hfT.htrl_ge hfT.hold hfT.hnew
            (fun h => absurd h hc_ne) (fun _ => ⟨by k6_field; exact hc_lt, hfal⟩) hmT
        c0_hsplit
        · have hw_ne : w ≠ 0xFFFFFFFF#32 := ‹_›
          obtain ⟨w0, todo', hw0_wn, htodo_eq, hw_eq, hw0_nc, hw0_mc, hwnat, hcid_eq, hslot_eq,
            hsz2, har_l, hbv_nv, hbv_mem, hbin_iff, hbin_other, htail_wc⟩ :=
            hcurW.step_unfold hclW.nc_le hnlW hw_ne
          have hw_sz : w.toNat < sz2Cl L := by unfold sz2Cl; omega
          have hcid_cl : w0 / 2 < szCl L := by unfold szCl K6Layout.maxCl at *; omega
          have hbv_sz : ((stw.wblit[w.toNat]?.getD 0#32) &&& 0x7FFFFFFF#32).toNat < sz2V L := by
            unfold sz2V; have := hclW.nv_le; rw [hwnat]; omega
          have har_nl : (stw.arena[k6ClauseOff stw (w0 / 2) + w0 % 2]?.getD 0#32).toNat = nl.toNat :=
            har_l
          have hcid_nc : w0 / 2 < stw.nc.toNat := by omega
          have hw_div_ne : (w >>> (1 : Nat)) ≠ 0xFFFFFFFF#32 := by
            intro h; have h1 := congrArg BitVec.toNat h
            rw [hcid_eq] at h1; unfold K6Layout.maxCl dimacsBound at hac_b; have := hclW.nc_le
            change w0 / 2 = 4294967295 at h1; omega
          c0_hsteps_nogrp
          · -- `vals[bv] == 1u`
            have hcur' := k6WatchSkip_cursor hshW (hw_eq ▸ htodo_eq ▸ hcurW) hw0_wn
            exact hJw (stw, nl, ticks', visits + 1#64, w, stw.wnext[w.toNat]?.getD 0#32,
                chains, done ++ [w0], todo') _
              (by dsimp only; rw [htodo_eq]; simp)
              ⟨hfw, hnl_lit, hpr_w, hnlW, hnl_fal, by rw [hwnat, hw_eq]; exact hcur', hmw⟩
          · -- Binary watch conflict (`vals[bv] == 2u`)
            have hbin_nz : (stw.wblit[w.toNat]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32 := ‹_›
            have hsz2_eq : k6ClauseSize stw (w0 / 2) = 2 := hbin_iff.mp (hwnat ▸ hbin_nz)
            have hbv_eq_ar := hbin_other hsz2_eq
            have hbv_fal : stw.vals[(stw.wblit[w0]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat]? = some 2#32 := by
              have hlt_bv : (stw.wblit[w0]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat < stw.vals.length := by
                rw [hshW.vals_len]; have := hclW.nv_le; omega
              have h2 : stw.vals[(stw.wblit[w.toNat]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat]?.getD 0#32 = 2#32 := ‹_›
              rw [hwnat, List.getElem?_eq_getElem hlt_bv, Option.getD_some] at h2
              rw [List.getElem?_eq_getElem hlt_bv, h2]
            have hall_fal : ∀ l ∈ k6ClauseLits stw (w0 / 2), stw.vals[l]? = some 2#32 := by
              intro l hl
              rw [k6_mem_clauseLits_iff
                  (by rw [hshW.arena_len]; exact Nat.le_trans (hclW.cl_wf _ hcid_nc).2.1 hclW.alen_le),
                hsz2_eq] at hl
              obtain ⟨idx, hidx, rfl⟩ := hl
              have hx2 : idx = w0 % 2 ∨ idx = w0 % 2 ^^^ 1 := by
                rcases Nat.mod_two_eq_zero_or_one w0 with hm | hm <;> simp [hm] <;> omega
              rcases hx2 with rfl | rfl
              · rw [har_nl]; exact hnl_fal
              · rw [← hbv_eq_ar]; exact hbv_fal
            exact ret_confl (w >>> (1 : Nat)) (ticks' + ((visits + 1#64) >>> (4 : Nat)) + 1#64) mw
              hmw hw_div_ne (by rw [hcid_eq]; exact hcid_nc) (by rw [hcid_eq]; exact hall_fal)
          · -- Binary watch unit (`vals[bv] == 0u` since `≠ 1` and `≠ 2`)
            have hbin_nz : (stw.wblit[w.toNat]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32 := ‹_›
            have hsz2_eq : k6ClauseSize stw (w0 / 2) = 2 := hbin_iff.mp (hwnat ▸ hbin_nz)
            have hbv_eq_ar := hbin_other hsz2_eq
            have hbv0 : stw.vals[(stw.wblit[w0]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat]? = some 0#32 := by
              have h1 : stw.vals[(stw.wblit[w.toNat]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat]?.getD 0#32 ≠ 1#32 := ‹_›
              have h2 : stw.vals[(stw.wblit[w.toNat]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat]?.getD 0#32 ≠ 2#32 := ‹_›
              have hlt_bv : (stw.wblit[w0]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat < stw.vals.length := by
                rw [hshW.vals_len]; have := hclW.nv_le; omega
              rw [hwnat] at h1 h2
              rcases hfw.hinv.assign.vals_dom _ hbv_nv with hz | ho | ht
              · rw [List.getElem?_eq_getElem hlt_bv]
                rw [List.getElem?_eq_getElem hlt_bv, Option.getD_some] at hz
                rw [hz]
              · rw [ho] at h1; exact absurd rfl h1
              · rw [ht] at h2; exact absurd rfl h2
            let bv := stw.wblit[w.toNat]?.getD 0#32 &&& 0x7FFFFFFF#32
            refine LeanQbe.T.wp_unroll_group fun Jdone hJdone => ?_
            c0_hsteps_nogrp
            · have hbv_toNat : bv.toNat < 2 * stw.nv.toNat := by dsimp only [bv]; rw [hwnat]; exact hbv_nv
              have hbv_z' : stw.vals[bv.toNat]? = some 0#32 := by dsimp only [bv]; rw [hwnat]; exact hbv0
              have hte_lt := k6_trl_end_lt_of_unassigned hshW hclW.nv_le hfw.hinv.assign hbv_toNat
                (by rw [hbv_z']; rfl)
              k6_call hAssign
              refine ⟨L, stw, _, hshW, hclW.max_v_eq, by have := hclW.nv_le; omega,
                by have := hclW.nv_le; omega, (k6MemA_to_mem hmw).2, fun m' hm' => ?_⟩
              have hmem_bv : bv.toNat ∈ k6ClauseLits stw (w0 / 2) := by
                dsimp only [bv]; rw [hwnat]; exact hbv_mem
              have hoth_bv : ∀ x ∈ k6ClauseLits stw (w0 / 2), x ≠ bv.toNat → stw.vals[x]? = some 2#32 := by
                intro x hx hne
                rw [k6_mem_clauseLits_iff
                    (by rw [hshW.arena_len]; exact Nat.le_trans (hclW.cl_wf _ hcid_nc).2.1 hclW.alen_le),
                  hsz2_eq] at hx
                obtain ⟨idx, hidx, rfl⟩ := hx
                have hx2 : idx = w0 % 2 ∨ idx = w0 % 2 ^^^ 1 := by
                  rcases Nat.mod_two_eq_zero_or_one w0 with hm | hm <;> simp [hm] <;> omega
                rcases hx2 with rfl | rfl
                · rw [har_nl]; exact hnl_fal
                · exfalso; apply hne; dsimp only [bv]; rw [hwnat]; exact hbv_eq_ar.symm
              have hfw' := m8_k6AssignStep_propFrame hfw hbv_toNat hbv_z' hcid_nc hmem_bv hoth_bv
              have hcid_bv : BitVec.ofNat 32 (w0 / 2) = w >>> (1 : Nat) := by
                apply BitVec.eq_of_toNat_eq; rw [hcid_eq, BitVec.toNat_ofNat]
                exact Nat.mod_eq_of_lt (by have := stw.nc.isLt; omega)
              rw [hcid_bv] at hfw'
              have hmA' := k6Mem_to_amem hfw'.hinv.shapes hm'
              have hnl_ne1 : nl.toNat ≠ bv.toNat := fun h => by
                rw [h, hbv_z'] at hnl_fal; cases hnl_fal
              have hnl_ne2 : nl.toNat ≠ (bv ^^^ 1#32).toNat := fun h => by
                have hbv_neg := k6_bv32_xor1_lt hbv_toNat
                have hne2 : stw.vals[(bv ^^^ 1#32).toNat]?.getD 0#32 ≠ 2#32 := by
                  intro h2'
                  have h1 : stw.vals[bv.toNat]?.getD 0#32 = 1#32 :=
                    (hfw.hinv.assign.vals_neg_iff bv.toNat hbv_toNat).mpr (by
                      change stw.vals[litNeg bv.toNat]?.getD 0#32 = 2#32
                      rw [← hbv_neg.1]; exact h2')
                  rw [hbv_z'] at h1; simp at h1
                exact hne2 (by rw [← h, hnl_fal]; rfl)
              have hnl_fal' : (k6AssignStep stw bv (w >>> (1 : Nat))).vals[nl.toNat]? = some 2#32 := by
                dsimp only [k6AssignStep]
                rw [List.getElem?_set_ne hnl_ne2.symm, List.getElem?_set_ne hnl_ne1.symm]
                exact hnl_fal
              have hcur'' := m8_k6WChainCursor_assignStep (hw_eq ▸ htodo_eq ▸ hcurW) bv (w >>> (1 : Nat))
              have hcur''' := k6WatchSkip_cursor hfw'.hinv.shapes hcur'' hw0_wn
              c0_hsteps!
              exact hJw (k6AssignStep stw bv (w >>> (1 : Nat)), nl, ticks', visits + 1#64, w,
                  (k6AssignStep stw bv (w >>> (1 : Nat))).wnext[w.toNat]?.getD 0#32,
                  chains, done ++ [w0], todo') _
                (by dsimp only; rw [htodo_eq]; simp)
                ⟨hfw', hnl_lit, hpr_w, hnlW, hnl_fal',
                  (by
                    rw [hwnat]
                    exact (congrArg (fun p => K6WChainCursor (k6AssignStep stw bv (w >>> (1 : Nat)))
                      nl.toNat chains (done ++ [w0]) todo' p
                      ((k6AssignStep stw bv (w >>> (1 : Nat))).wnext[w0]?.getD 0#32)) hw_eq).mpr hcur'''),
                  hmA'⟩
            · have hfalse : stw.vals[(stw.wblit[w.toNat]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat]? = some 0#32 := by
                rw [hwnat]; exact hbv0
              have hc' : stw.vals[(stw.wblit[w.toNat]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat]?.getD 0#32 ≠ 0#32 := ‹_›
              rw [hfalse] at hc'; exact absurd rfl hc'
          · -- Non-binary watch (`wb &&& 0x80000000 = 0`)
            have hbin_z : (stw.wblit[w.toNat]?.getD 0#32 &&& 0x80000000#32) = 0#32 := ‹_›
            have hsz_ne2 : k6ClauseSize stw (w0 / 2) ≠ 2 := fun h2 =>
              absurd (hbin_iff.mpr h2) (by rw [← hwnat, hbin_z]; simp)
            have hwf_c := hclW.cl_wf (w0 / 2) hcid_nc
            have har_ok : ∀ idx < k6ClauseSize stw (w0 / 2),
                k6ClauseOff stw (w0 / 2) + idx < L.acap ∧
                (stw.arena[k6ClauseOff stw (w0 / 2) + idx]?.getD 0#32).toNat < 2 * stw.nv.toNat := by
              intro idx hidx
              exact ⟨by have := hclW.alen_le; omega,
                hwf_c.2.2.1 _ (by
                  rw [k6_mem_clauseLits_iff
                    (by rw [hshW.arena_len]; exact Nat.le_trans hwf_c.2.1 hclW.alen_le)]
                  exact ⟨idx, hidx, rfl⟩)⟩
            have hother_slot_lt : w0 % 2 ^^^ 1 < 2 := by
              rcases Nat.mod_two_eq_zero_or_one w0 with h | h <;> simp [h]
            let other := stw.arena[k6ClauseOff stw (w0 / 2) + (w0 % 2 ^^^ 1)]?.getD 0#32
            have hother_nv : other.toNat < 2 * stw.nv.toNat := (har_ok _ (by omega)).2
            have hot_mem : other.toNat ∈ k6ClauseLits stw (w0 / 2) := by
              rw [k6_mem_clauseLits_iff (by rw [hshW.arena_len]; exact Nat.le_trans hwf_c.2.1 hclW.alen_le)]
              exact ⟨w0 % 2 ^^^ 1, by omega, rfl⟩
            have hw_sh1 : (w >>> (1 : Nat)).toNat = w0 / 2 := hcid_eq
            have hw_m2_lt : w0 % 2 < 2 ^ 32 := Nat.lt_trans (Nat.mod_lt w0 (by decide)) (by decide)
            have hm2_xor_lt : w0 % 2 ^^^ 1 < 2 ^ 32 := by
              rcases Nat.mod_two_eq_zero_or_one w0 with h | h <;> simp [h]
            have hslot_bv : (w &&& (1 : BitVec 32)) = BitVec.ofNat 32 (w0 % 2) := by
              apply BitVec.eq_of_toNat_eq
              change (w &&& 1#32).toNat = (BitVec.ofNat 32 (w0 % 2)).toNat
              rw [hslot_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw_m2_lt]
            have hslot_other_bv :
                (w &&& (1 : BitVec 32) ^^^ (1 : BitVec 32)) = BitVec.ofNat 32 (w0 % 2 ^^^ 1) := by
              apply BitVec.eq_of_toNat_eq
              rw [BitVec.toNat_xor, show (w &&& (1 : BitVec 32)).toNat = (w &&& 1#32).toNat from rfl,
                hslot_eq, show (1 : BitVec 32).toNat = 1 from rfl, BitVec.toNat_ofNat,
                Nat.mod_eq_of_lt hm2_xor_lt]
            have hcl_off_add :
                (stw.clOff[w0 / 2]?.getD 0#32 + (w &&& (1 : BitVec 32) ^^^ (1 : BitVec 32))).toNat =
                k6ClauseOff stw (w0 / 2) + (w0 % 2 ^^^ 1) := by
              have hcap' := (har_ok (w0 % 2 ^^^ 1) (by omega)).1
              unfold k6ClauseOff at hcap' ⊢; unfold dimacsBound at hac_b
              rw [hslot_other_bv]; have := hm2_xor_lt; bv_omega
            have hcl_off_ar :
                ((stw.clOff[(w >>> (1 : Nat)).toNat]?.getD 0#32) +
                  (w &&& (1 : BitVec 32) ^^^ (1 : BitVec 32))).toNat < szAr L := by
              unfold szAr; rw [hw_sh1, hcl_off_add]; exact (har_ok (w0 % 2 ^^^ 1) (by omega)).1
            have hother_mv2 : other.toNat < sz2V L := by unfold sz2V; have := hclW.nv_le; omega
            have hother_mv2' :
                (stw.arena[(stw.clOff[(w >>> (1 : Nat)).toNat]?.getD 0#32 +
                  (w &&& (1 : BitVec 32) ^^^ (1 : BitVec 32))).toNat]?.getD 0#32).toNat < sz2V L := by
              rw [hw_sh1, hcl_off_add]; exact hother_mv2
            have hw_div_ar : (w >>> (1 : Nat)).toNat < szCl L := by rw [hw_sh1]; exact hcid_cl
            have hwc : K6WChainCursor stw nl.toNat chains done (w0 :: todo') prev (BitVec.ofNat 32 w0) :=
              hw_eq ▸ htodo_eq ▸ hcurW
            c0_hsteps_nogrp
            · -- `vals[other] == 1u`
              obtain ⟨hkp_inv, hkp_wc⟩ :=
                k6WatchKeep_preserves hfw.hinv hnlW hwc hother_nv hot_mem hsz_ne2
              have hfw' := m8_k6PropFrame_watchStep hfw hkp_inv
                rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
              c0_hsteps!
              refine hJw (stw.putArr .wblit w0 other, nl, ticks' + 1#64, visits + 1#64, w,
                  stw.wnext[w.toNat]?.getD 0#32, chains, done ++ [w0], todo') _
                (by dsimp only; rw [htodo_eq]; simp)
                ⟨hfw', hnl_lit, hpr_w, hnlW, hnl_fal, by rw [hwnat, hw_eq]; exact hkp_wc, ?_⟩
              refine Eq.mp (congrArg (fun x => (K6MemA L kp x ⋆ _) _) ?_) ‹_›
              k6_ext <;> (first | rfl | {
                dsimp only [other]; try rw [hwnat]; try rw [hw_sh1]; try rw [hcl_off_add]
                try dsimp only [k6ClauseOff]; try rfl })
            · -- `vals[other] ≠ 1u`: search `[2..sz)` for non-falsified replacement
              have hidx_eq :
                  ((stw.clOff[w.toNat / 2]?.getD 0#32).toNat + (w.toNat % 2 ^^^ 1)) % 4294967296 =
                  k6ClauseOff stw (w0 / 2) + (w0 % 2 ^^^ 1) := by
                have hb :
                    ((stw.clOff[w.toNat / 2]?.getD 0#32).toNat + (w &&& 1#32 ^^^ 1#32).toNat) % 2 ^ 32 =
                    k6ClauseOff stw (w0 / 2) + (w0 % 2 ^^^ 1) := by
                  rw [hwnat, ← BitVec.toNat_add]; exact hcl_off_add
                simpa using hb
              have hother_ne1 : stw.vals[other.toNat]?.getD 0#32 ≠ 1#32 := by
                simpa [hidx_eq, other] using hc
              let sz := stw.clSz[w0 / 2]?.getD 0#32
              let off := stw.clOff[w0 / 2]?.getD 0#32
              refine wp_while_break_state
                (projBrk := fun b : BitVec 32 × BitVec 32 × BitVec 32 => (b.1, b.2.1, b.2.2, ()))
                (fun b mb => mb = mw ∧
                  (b.2.1 = 0xFFFFFFFF#32 ∧
                      (∀ j, 2 ≤ j → j < sz.toNat →
                        stw.vals[(stw.arena[off.toNat + j]?.getD 0#32).toNat]? = some 2#32) ∨
                    (2 ≤ b.2.1.toNat ∧ b.2.1.toNat < sz.toNat ∧
                      b.2.2 = stw.arena[off.toNat + b.2.1.toNat]?.getD 0#32 ∧
                      stw.vals[b.2.2.toNat]? ≠ some 2#32)))
                (projLp := fun r : BitVec 32 => (r, ())) (fun r => sz.toNat - r.toNat)
                (fun r m'' => m'' = mw ∧ r.toNat ≤ sz.toNat ∧ 2 ≤ r.toNat ∧
                  ∀ j, 2 ≤ j → j < r.toNat →
                    stw.vals[(stw.arena[off.toNat + j]?.getD 0#32).toNat]? = some 2#32) ?_ ?_ ?_
              · rintro Br ⟨_, ri, repl⟩ mb ⟨rfl, hbrk⟩
                dsimp only at hbrk ⊢
                c0_hsplit
                · -- Relocate watch (`ri != 0xFFFFFFFFu`)
                  have hri_ne : ri ≠ 0xFFFFFFFF#32 := by bv_omega
                  rcases hbrk with ⟨habs, _⟩ | ⟨hri_ge, hri_lt, hrepl_eq, hrepl_nf⟩
                  · exact absurd habs hri_ne
                  have hrepl_ne' : repl.toNat ≠ nl.toNat := fun h => by
                    rw [h, hnl_fal] at hrepl_nf; exact hrepl_nf rfl
                  obtain ⟨hrl_inv, ⟨chW', hwc'⟩⟩ :=
                    k6WatchReloc_preserves hfw.hinv hnlW hwc hri_ge hri_lt hrepl_ne' rfl hrepl_eq
                  have hfw' := m8_k6PropFrame_watchStep hfw hrl_inv
                    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
                  obtain ⟨hri_cap, _⟩ := har_ok ri.toNat hri_lt
                  obtain ⟨hslot_cap, _⟩ := har_ok (w0 % 2) (by have := Nat.mod_lt w0 (by decide : 0 < 2); omega)
                  have hslot_off_eq :
                      (stw.clOff[w0 / 2]?.getD 0#32 + (w &&& (1 : BitVec 32))).toNat =
                      (stw.clOff[w0 / 2]?.getD 0#32).toNat + w0 % 2 := by
                    rw [hslot_bv]; unfold dimacsBound at hac_b
                    change (stw.clOff[w0 / 2]?.getD 0#32 + BitVec.ofNat 32 (w0 % 2)).toNat = _
                    change k6ClauseOff stw (w0 / 2) + w0 % 2 < L.acap at hslot_cap
                    unfold k6ClauseOff at hslot_cap; bv_omega
                  have hslot_ar :
                      (stw.clOff[(w >>> (1 : Nat)).toNat]?.getD 0#32 +
                        (w &&& (1 : BitVec 32))).toNat < szAr L := by
                    unfold szAr; rw [hw_sh1, hslot_off_eq]; exact hslot_cap
                  have hri_off_eq :
                      (stw.clOff[w0 / 2]?.getD 0#32 + ri).toNat =
                      (stw.clOff[w0 / 2]?.getD 0#32).toNat + ri.toNat := by
                    unfold dimacsBound at hac_b
                    change k6ClauseOff stw (w0 / 2) + ri.toNat < L.acap at hri_cap
                    unfold k6ClauseOff at hri_cap; bv_omega
                  have hri_ar :
                      (stw.clOff[(w >>> (1 : Nat)).toNat]?.getD 0#32 + ri).toNat < szAr L := by
                    unfold szAr; rw [hw_sh1, hri_off_eq]; exact hri_cap
                  have hrepl_mv2 : repl.toNat < sz2V L := by
                    change repl = stw.arena[k6ClauseOff stw (w0 / 2) + ri.toNat]?.getD 0#32 at hrepl_eq
                    rw [hrepl_eq]; unfold sz2V; have := hclW.nv_le; omega
                  have hnl_bn : BitVec.ofNat 32 nl.toNat = nl := by simp
                  have hprv_lt : prev ≠ 0xFFFFFFFF#32 → prev.toNat < sz2Cl L := fun hp => by
                    rcases hwc.prev_rel with ⟨_, hpf, _⟩ | ⟨_, u, _, hp_eq, hu_len, _⟩
                    · exact absurd hpf hp
                    · rw [hshW.wnext_len] at hu_len
                      have hu32 : u < 2 ^ 32 := by
                        have hmx := L.hmaxV
                        try unfold sz2Cl at hu_len
                        try unfold K6Layout.maxCl at hu_len
                        omega
                      rw [hp_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hu32]
                      unfold sz2Cl; exact hu_len
                  c0_hsteps_nogrp
                  try refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
                  c0_hsplit
                  · have hpeq : prev = 0xFFFFFFFF#32 := by bv_omega
                    c0_hsteps!
                    refine hJw (_, nl, ticks' + 1#64, visits + 1#64, prev, stw.wnext[w.toNat]?.getD 0#32,
                        chW', done, todo') _ (by dsimp only; rw [htodo_eq]; simp)
                      ⟨hfw', hnl_lit, by dsimp only [k6WatchStep0]; exact hpr_w, hnlW,
                        by dsimp only [k6WatchStep0]; exact hnl_fal,
                        by rw [hwnat]; exact hwc', ?_⟩
                    refine Eq.mp (congrArg (fun x => (K6MemA L kp x ⋆ _) _) ?_) ‹_›
                    dsimp only [k6WatchStep0, k6ClauseOff]; simp only [hpeq, ↓reduceIte]
                    have hnl_lit' : st.trl[st.prop.toNat]?.getD 0#32 ^^^ 1 = nl := hnl_lit.symm
                    have hw_cid1 : (w >>> OfNat.ofNat 1).toNat = w0 / 2 := hcid_eq
                    have hbv_w0 : (BitVec.ofNat 32 w0).toNat = w0 := hw_eq ▸ hwnat
                    k6_ext <;> (first | rfl | {
                      (try simp only [hw_cid1, hwnat, hcl_off_add, hslot_off_eq, hri_off_eq, hnl_lit', hnl_bn])
                      (try rw [hbv_w0])
                      (try rw [hw_eq])
                      (try dsimp only [k6ClauseOff])
                      (try rfl) })
                  · have hpne : prev ≠ 0xFFFFFFFF#32 := by bv_omega
                    have hprv_bd := hprv_lt hpne
                    c0_hsteps!
                    refine hJw (_, nl, ticks' + 1#64, visits + 1#64, prev, stw.wnext[w.toNat]?.getD 0#32,
                        chW', done, todo') _ (by dsimp only; rw [htodo_eq]; simp)
                      ⟨hfw', hnl_lit, by dsimp only [k6WatchStep0]; exact hpr_w, hnlW,
                        by dsimp only [k6WatchStep0]; exact hnl_fal,
                        by rw [hwnat]; exact hwc', ?_⟩
                    refine Eq.mp (congrArg (fun x => (K6MemA L kp x ⋆ _) _) ?_) ‹_›
                    dsimp only [k6WatchStep0, k6ClauseOff]; simp only [hpne, ↓reduceIte]
                    have hnl_lit' : st.trl[st.prop.toNat]?.getD 0#32 ^^^ 1 = nl := hnl_lit.symm
                    have hw_cid1 : (w >>> OfNat.ofNat 1).toNat = w0 / 2 := hcid_eq
                    have hbv_w0 : (BitVec.ofNat 32 w0).toNat = w0 := hw_eq ▸ hwnat
                    k6_ext <;> (first | rfl | {
                      (try simp only [hw_cid1, hwnat, hcl_off_add, hslot_off_eq, hri_off_eq, hnl_lit', hnl_bn])
                      (try rw [hbv_w0])
                      (try rw [hw_eq])
                      (try dsimp only [k6ClauseOff])
                      (try rfl) })
                · -- No replacement (`ri = 0xFFFFFFFFu`): keep watch with `other` & conflict/unit check
                  have hrieq : ri = 0xFFFFFFFF#32 := by bv_omega
                  rcases hbrk with ⟨_, hall_r2⟩ | ⟨hri_ge, hri_lt, _⟩
                  · obtain ⟨hkp_inv, hkp_wc⟩ :=
                      k6WatchKeep_preserves hfw.hinv hnlW hwc hother_nv hot_mem hsz_ne2
                    have hfw' := m8_k6PropFrame_watchStep hfw hkp_inv
                      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
                    have hmem_other : other.toNat < stw.vals.length := by
                      rw [hshW.vals_len]; exact hother_mv2
                    have hoth_sz : other.toNat < sz2V L := hother_mv2
                    let hw' := stw.putArr .wblit w0 other
                    have hall_other_fal : ∀ l ∈ k6ClauseLits hw' (w0 / 2),
                        l ≠ other.toNat → hw'.vals[l]? = some 2#32 := by
                      intro l hl hne
                      change l ∈ k6ClauseLits stw (w0 / 2) at hl
                      rw [k6_mem_clauseLits_iff
                        (by rw [hshW.arena_len]; exact Nat.le_trans hwf_c.2.1 hclW.alen_le)] at hl
                      obtain ⟨idx, hidx, rfl⟩ := hl
                      change stw.vals[(stw.arena[off.toNat + idx]?.getD 0#32).toNat]? = some 2#32
                      by_cases h01 : idx < 2
                      · have hx2 : idx = w0 % 2 ∨ idx = w0 % 2 ^^^ 1 := by
                          rcases Nat.mod_two_eq_zero_or_one w0 with hm | hm <;> simp [hm] <;> omega
                        rcases hx2 with rfl | rfl
                        · change stw.vals[(stw.arena[k6ClauseOff stw (w0 / 2) +
                            w0 % 2]?.getD 0#32).toNat]? = some 2#32
                          rw [har_nl]; exact hnl_fal
                        · exfalso; exact hne rfl
                      · exact hall_r2 idx (by omega) hidx
                    c0_hsteps_nogrp
                    · -- `ov == 2u`: conflict!
                      have hov2 : hw'.vals[other.toNat]? = some 2#32 := by
                        have h2 : stw.vals[(stw.arena[k6ClauseOff stw (w0 / 2) +
                            (w0 % 2 ^^^ 1)]?.getD 0#32).toNat]?.getD 0#32 = 2#32 := by
                          simpa [K6State.putArr, hidx_eq] using hc
                        dsimp only [hw', K6State.putArr, other]
                        rw [List.getElem?_eq_getElem hmem_other, Option.getD_some] at h2
                        rw [List.getElem?_eq_getElem hmem_other, h2]
                      have hall_fal' : ∀ l ∈ k6ClauseLits hw' (w0 / 2), hw'.vals[l]? = some 2#32 := by
                        intro l hl
                        by_cases he : l = other.toNat
                        · subst he; exact hov2
                        · exact hall_other_fal l hl he
                      have hw_cid1 : (w >>> OfNat.ofNat 1).toNat = w0 / 2 := hcid_eq
                      have hmw_kp : (K6MemA L kp hw' ⋆ P) m := by
                        refine Eq.mp (congrArg (fun x => (K6MemA L kp x ⋆ P) m) ?_) hm
                        k6_ext <;> (first | rfl | {
                          dsimp only [hw', K6State.putArr, other]
                          (try rw [hwnat]); (try rw [hw_cid1]); (try rw [hw_sh1]); (try rw [hcl_off_add])
                          (try dsimp only [k6ClauseOff]); (try rfl) })
                      k6_call hAddTicks
                      refine ⟨L, hw', _, hfw'.hinv.shapes, (k6MemA_to_mem hmw_kp).2, fun tk' mT hmT => ?_⟩
                      have hfT := m8_k6PropFrame_ticks hfw' tk'
                      c0_hsteps!
                      exact hQ (w >>> (1 : Nat)) _ mT hfT.hinv hfT.hsync hfT.hpres hfT.htrl_ge hfT.hold hfT.hnew
                        (fun h => absurd h hw_div_ne)
                        (fun _ => ⟨by rw [hcid_eq]; exact hcid_nc,
                          by rw [hcid_eq]; intro l hl; exact hall_fal' l hl⟩)
                        hmT
                    · -- `ov == 0u`: unit!
                      have hoth0 : hw'.vals[other.toNat]? = some 0#32 := by
                        have hdom := hfw.hinv.assign.vals_dom other.toNat hother_nv
                        have hne1 : stw.vals[other.toNat]?.getD 0#32 ≠ 1#32 := hother_ne1
                        have hne2 : stw.vals[other.toNat]?.getD 0#32 ≠ 2#32 := by
                          simpa [K6State.putArr, hidx_eq, other] using hc
                        rw [List.getElem?_eq_getElem hmem_other, Option.getD_some] at hne1 hne2
                        dsimp only [hw', K6State.putArr]
                        rw [List.getElem?_eq_getElem hmem_other]
                        rcases hdom with hz | ho | ht
                        · rw [List.getElem?_eq_getElem hmem_other, Option.getD_some] at hz; rw [hz]
                        · rw [List.getElem?_eq_getElem hmem_other, Option.getD_some] at ho; exact absurd ho hne1
                        · rw [List.getElem?_eq_getElem hmem_other, Option.getD_some] at ht; exact absurd ht hne2
                      have hte_lt := k6_trl_end_lt_of_unassigned hfw'.hinv.shapes hfw'.hinv.clauses.nv_le
                        hfw'.hinv.assign hother_nv (by rw [hoth0]; rfl)
                      have hw_cid1 : (w >>> OfNat.ofNat 1).toNat = w0 / 2 := hcid_eq
                      have hmw_kp : (K6MemA L kp hw' ⋆ P) m := by
                        refine Eq.mp (congrArg (fun x => (K6MemA L kp x ⋆ P) m) ?_) hm
                        k6_ext <;> (first | rfl | {
                          dsimp only [hw', K6State.putArr, other]
                          (try rw [hwnat]); (try rw [hw_cid1]); (try rw [hw_sh1]); (try rw [hcl_off_add])
                          (try dsimp only [k6ClauseOff]); (try rfl) })
                      have hw_sh1_str : (w &&& 1 ^^^ 1).toNat = w0 % 2 ^^^ 1 := by
                        rw [hslot_other_bv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm2_xor_lt]
                      have hother_c0 :
                          stw.arena[(stw.clOff[(w >>> OfNat.ofNat 1).toNat]?.getD 0#32 +
                            (w &&& 1 ^^^ 1)).toNat]?.getD 0#32 = other := by
                        have hx1 : w0 % 2 ^^^ 1 ≤ 1 := by
                          rcases Nat.mod_two_eq_zero_or_one w0 with h | h <;> simp [h]
                        have hdim : dimacsBound < 2 ^ 32 := by decide
                        have hsum_lt : (stw.clOff[w0 / 2]?.getD 0#32).toNat + (w0 % 2 ^^^ 1) < 2 ^ 32 := by
                          have h1 := hclW.alen_le
                          have h2 := hwf_c.2.1
                          have h3 := hwf_c.1
                          have h4 := L.hacap.2
                          change k6ClauseOff stw (w0 / 2) + k6ClauseSize stw (w0 / 2) ≤ stw.alen.toNat at h2
                          change (stw.clOff[w0 / 2]?.getD 0#32).toNat + k6ClauseSize stw (w0 / 2) ≤
                            stw.alen.toNat at h2
                          omega
                        have hidx_bv : (stw.clOff[(w >>> OfNat.ofNat 1).toNat]?.getD 0#32 +
                            (w &&& 1 ^^^ 1)).toNat =
                            (stw.clOff[w0 / 2]?.getD 0#32).toNat + (w0 % 2 ^^^ 1) := by
                          rw [hw_cid1, BitVec.toNat_add, hw_sh1_str]
                          exact Nat.mod_eq_of_lt hsum_lt
                        rw [hidx_bv]; rfl
                      have hw_sh1_bv : (w >>> OfNat.ofNat 1) = w >>> (1 : Nat) := by
                        apply BitVec.eq_of_toNat_eq; exact hw_cid1.trans hw_sh1.symm
                      refine LeanQbe.T.wp_unroll_group fun Jdone hJdone => ?_
                      c0_hsteps_nogrp
                      c0_hsplit
                      · k6_call hAssign
                        refine ⟨L, hw', _, hfw'.hinv.shapes, hfw'.hinv.clauses.max_v_eq,
                          by rw [hother_c0]; exact hother_mv2,
                          by have := hfw'.hinv.clauses.nv_le
                             dsimp only [hw', K6State.putArr] at hte_lt ⊢
                             exact Nat.lt_of_lt_of_le hte_lt this,
                          (k6MemA_to_mem hmw_kp).2, fun mA' hmA' => ?_⟩
                        have hfw'' := m8_k6AssignStep_propFrame hfw' hother_nv hoth0 hcid_nc hot_mem hall_other_fal
                        have hcid_bv : BitVec.ofNat 32 (w0 / 2) = w >>> (1 : Nat) := by
                          apply BitVec.eq_of_toNat_eq; rw [hcid_eq, BitVec.toNat_ofNat]
                          exact Nat.mod_eq_of_lt (by have := stw.nc.isLt; omega)
                        rw [hcid_bv] at hfw''
                        rw [hother_c0, hw_sh1_bv] at hmA'
                        have hmAA' := k6Mem_to_amem hfw''.hinv.shapes hmA'
                        have hnl_ne1 : nl.toNat ≠ other.toNat := fun h => by
                          have hoth0' : stw.vals[other.toNat]? = some 0#32 := hoth0
                          rw [h, hoth0'] at hnl_fal; cases hnl_fal
                        have hnl_ne2 : nl.toNat ≠ (other ^^^ 1#32).toNat := fun h => by
                          have hov_neg := k6_bv32_xor1_lt hother_nv
                          have h1 : stw.vals[other.toNat]?.getD 0#32 = 1#32 :=
                            (hfw.hinv.assign.vals_neg_iff other.toNat hother_nv).mpr (by
                              change stw.vals[litNeg other.toNat]?.getD 0#32 = 2#32
                              rw [← hov_neg.1, ← h]; rw [hnl_fal]; rfl)
                          rw [show stw.vals[other.toNat]?.getD 0#32 = 0#32 by
                            simpa [hw', K6State.putArr] using congrArg (Option.getD · 0#32) hoth0] at h1
                          simp at h1
                        have hnl_fal'' :
                            (k6AssignStep hw' other (w >>> (1 : Nat))).vals[nl.toNat]? = some 2#32 := by
                          dsimp only [k6AssignStep]
                          rw [List.getElem?_set_ne hnl_ne2.symm, List.getElem?_set_ne hnl_ne1.symm]
                          exact hnl_fal
                        have hcur''' := m8_k6WChainCursor_assignStep hkp_wc other (w >>> (1 : Nat))
                        c0_hsteps!
                        exact hJw (k6AssignStep hw' other (w >>> (1 : Nat)), nl, ticks' + 1#64, visits + 1#64, w,
                            stw.wnext[w.toNat]?.getD 0#32, chains, done ++ [w0], todo') _
                          (by dsimp only; rw [htodo_eq]; simp)
                          ⟨hfw'', hnl_lit, hpr_w, hnlW, hnl_fal'',
                            by rw [hwnat, hw_eq]; have hc' := hcur'''; rw [hw_eq] at hc'; exact hc',
                            hmAA'⟩
                      · have hc' : hw'.vals[other.toNat]?.getD 0#32 ≠ 0#32 := by
                          simpa [hw', K6State.putArr, hidx_eq, other] using hc
                        rw [hoth0] at hc'; exact absurd rfl hc'
                  · exfalso
                    have h429 : (0xFFFFFFFF#32 : BitVec 32).toNat = 4294967295 := rfl
                    rw [hrieq, h429] at hri_lt
                    have hwf_bd : k6ClauseSize stw (w0 / 2) ≤ stw.alen.toNat := by
                      have := hwf_c.2.1; omega
                    have hal := hclW.alen_le
                    have hsz_nat : sz.toNat = k6ClauseSize stw (w0 / 2) := rfl
                    rw [hsz_nat] at hri_lt
                    unfold K6Layout.acap at hac_b hal
                    unfold dimacsBound at hac_b
                    omega
              · intro B2 L2 r m1 hB2 ih1 ⟨rfl, hr_le, hr2, hall_j⟩
                dsimp only at hr_le hr2 hall_j ⊢
                c0_hsplit
                · have hr_lt : r.toNat < sz.toNat := by
                    have hc0 : r.toNat < (stw.clSz[w.toNat / 2]?.getD 0#32).toNat := by bv_omega
                    simpa only [sz, hwnat] using hc0
                  obtain ⟨hr_cap, hr_lit⟩ := har_ok r.toNat hr_lt
                  have hr_ar : (stw.clOff[(w >>> (1 : Nat)).toNat]?.getD 0#32 + r).toNat < szAr L := by
                    rw [hw_sh1]; unfold szAr dimacsBound at *
                    change k6ClauseOff stw (w0 / 2) + r.toNat < L.acap at hr_cap
                    unfold k6ClauseOff at hr_cap; bv_omega
                  have hcand_mv2 :
                      (stw.arena[(stw.clOff[(w >>> (1 : Nat)).toNat]?.getD 0#32 + r).toNat]?.getD
                        0#32).toNat < sz2V L := by
                    rw [hw_sh1]
                    have hco : (stw.clOff[w0 / 2]?.getD 0#32 + r).toNat =
                        k6ClauseOff stw (w0 / 2) + r.toNat := by
                      unfold k6ClauseOff at hr_cap ⊢; unfold dimacsBound at hac_b; bv_omega
                    rw [hco]; unfold sz2V; have := hclW.nv_le; omega
                  have hr1_wrap : (r + 1#32).toNat = r.toNat + 1 := by
                    have hsz_bd : sz.toNat < 2 ^ 28 := by
                      have := hclW.alen_le; unfold dimacsBound at hac_b
                      change k6ClauseSize stw (w0 / 2) < 2 ^ 28; omega
                    bv_omega
                  c0_hsteps_nogrp
                  · have hco : (stw.clOff[(w >>> (1 : Nat)).toNat]?.getD 0#32 + r).toNat =
                        off.toNat + r.toNat := by
                      rw [hw_sh1]; change (off + r).toNat = off.toNat + r.toNat; unfold off
                      unfold k6ClauseOff at hr_cap; unfold dimacsBound at hac_b; bv_omega
                    have hc_nf : stw.vals[(stw.arena[off.toNat + r.toNat]?.getD 0#32).toNat]? ≠ some 2#32 := by
                      have hc0 : stw.vals[(stw.arena[(stw.clOff[(w >>> (1 : Nat)).toNat]?.getD 0#32 +
                          r).toNat]?.getD 0#32).toNat]?.getD 0#32 ≠ 2#32 := ‹_›
                      rw [hco] at hc0
                      intro h2; apply hc0; rw [h2]; rfl
                    rw [hco]
                    exact hB2 (r, r, stw.arena[off.toNat + r.toNat]?.getD 0#32) _
                      ⟨rfl, Or.inr ⟨hr2, hr_lt, rfl, hc_nf⟩⟩
                  · have hco : (stw.clOff[(w >>> (1 : Nat)).toNat]?.getD 0#32 + r).toNat =
                        off.toNat + r.toNat := by
                      rw [hw_sh1]; change (off + r).toNat = off.toNat + r.toNat; unfold off
                      unfold k6ClauseOff at hr_cap; unfold dimacsBound at hac_b; bv_omega
                    have hc_f : stw.vals[(stw.arena[off.toNat + r.toNat]?.getD 0#32).toNat]? = some 2#32 := by
                      have hc0 : stw.vals[(stw.arena[(stw.clOff[(w >>> (1 : Nat)).toNat]?.getD 0#32 +
                          r).toNat]?.getD 0#32).toNat]?.getD 0#32 = 2#32 := ‹_›
                      have hvl : (stw.arena[off.toNat + r.toNat]?.getD 0#32).toNat < stw.vals.length := by
                        have hlt_lit :
                            (stw.arena[off.toNat + r.toNat]?.getD 0#32).toNat < 2 * stw.nv.toNat := hr_lit
                        rw [hshW.vals_len]; have := hclW.nv_le; omega
                      rw [hco, List.getElem?_eq_getElem hvl, Option.getD_some] at hc0
                      rw [List.getElem?_eq_getElem hvl, hc0]
                    refine ih1 (r + 1#32) _ (by rw [hr1_wrap]; omega) ⟨rfl, by rw [hr1_wrap]; omega,
                      by rw [hr1_wrap]; omega, fun j hj1 hj2 => ?_⟩
                    rw [hr1_wrap] at hj2
                    by_cases hjr : j = r.toNat
                    · subst hjr; exact hc_f
                    · exact hall_j j hj1 (by omega)
                · have hr_ge : sz.toNat ≤ r.toNat := by
                    have hc0 : ¬r.toNat < (stw.clSz[w.toNat / 2]?.getD 0#32).toNat := by bv_omega
                    simpa only [sz, hwnat] using Nat.le_of_not_lt hc0
                  c0_hsteps!
                  exact hB2 (r, 0xFFFFFFFF#32, 0#32) _
                    ⟨rfl, Or.inl ⟨rfl, fun j hj1 hj2 => hall_j j hj1 (by omega)⟩⟩
              · intro B2 L2 _ hL2; c0_hsteps!; exact hL2 2#32 mw ⟨rfl, hsz2, le_refl _, fun j hj1 hj2 => by
                  have h2n : (2#32 : BitVec 32).toNat = 2 := rfl
                  omega⟩
        · -- `w = 0xFFFFFFFF#32`: inner loop exit -> outer loop continue
          c0_hsteps!
          exact hJ (stw, ticks' + (visits >>> (4 : Nat)) + 1#64) mw
            (by
              dsimp only; rw [hpr_w, hpr1_wrap]
              have hnv_eq := congrArg BitVec.toNat hf_st.hpres.nv
              have hte_le := hf_st.hinv.assign.trl_end_le
              omega)
            ⟨hfw, hmw⟩
    · -- `st.prop ≥ st.trl_end`: outer loop exit -> `full_k6_add_ticks(k, ticks); return 0xFFFFFFFFu;`
      have hpeq : st.prop = st.trl_end :=
        BitVec.eq_of_toNat_eq (Nat.le_antisymm hf_st.hinv.assign.prop_le (by bv_omega))
      k6_call hAddTicks
      refine ⟨L, st, _, hsh0, (k6MemA_to_mem hm').2, fun tk' mT hmT => ?_⟩
      have hfT := m8_k6PropFrame_ticks hf_st tk'
      c0_hsteps!
      exact hQ 0xFFFFFFFF#32 _ mT hfT.hinv hfT.hsync hfT.hpres hfT.htrl_ge hfT.hold hfT.hnew
        (fun _ => by
          change (st.putHdr .ticks tk').prop = (st.putHdr .ticks tk').trl_end
          simpa [K6State.putHdr] using hpeq)
        (fun h => absurd rfl h) hmT

end LeanQbe.T.Examples.Kissat.FullM8SweepV2
