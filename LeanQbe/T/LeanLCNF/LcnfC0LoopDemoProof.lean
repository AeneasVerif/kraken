module

public import LeanQbe.T.LeanLCNF.LcnfC0LoopDemoProof4

/-!
# Dual-Arch WP Proof for `FactLoop` (`LcnfC0LoopDemoProof`)

Section 3b (part 2): `factStr_wp`, `factLoopLinkedMod_moduleOk`,
concrete `loopRtMem_ok`, and `fact25_str_spec`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF

open LeanQbe.T LeanQbe.T.Frontend.C0 LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open Std Std.ExtHashMap
open scoped LeanQbe.T.ProofUtil

private theorem natDigitsRev_len_le_of_lt_pow10 :
    ∀ k n : Nat, n < 10 ^ k → (natDigitsRev n).length ≤ k := by
  intro k
  induction k with
  | zero =>
    intro n hn
    have : n = 0 := by omega
    subst this
    rw [natDigitsRev.eq_def]
    simp
  | succ k ih =>
    intro n hn
    by_cases hn0 : n = 0
    · subst hn0
      rw [natDigitsRev.eq_def]
      simp
    · rw [natDigitsRev.eq_def, dite_eq_right hn0]
      simp only [List.length_cons]
      have hdiv : n / 10 < 10 ^ k :=
        Nat.div_lt_of_lt_mul (by rw [Nat.pow_succ'] at hn; omega)
      exact Nat.succ_le_succ (ih (n / 10) hdiv)

private theorem strAllocBytes_mono {a b : Nat} (h : a ≤ b) :
    strAllocBytes a ≤ strAllocBytes b := by
  unfold strAllocBytes align8
  omega

theorem factStr_wp (xs : Tup Val [i64, i64]) (m : Mem 64) (Q : Post [i64]) (X : XPost) :
    factStrSpec xs m Q X → Func.wp factLoopEnv (factLoopTfs.tf_1.toFn).body xs m Q X := by
  rcases xs with ⟨rt, n, ⟨⟩⟩
  rintro ⟨st, scr, scrLimbs, k, R, hkLt, rfl, hwf, hwkCap, hscrCap, hmaxLimb, hcases, hremB, hm,
    hk⟩
  let resVal := FactLoop.factAcc k 1
  change wp factLoopEnv Q X
    (.call "l_LeanQbe_T_LeanLCNF_FactLoop_factAcc" (as := [i64, i64, i64]) (bs := [i64])
      (.var rt, .var (boxNat k), .imm 3#64, ()) fun v0 =>
    .call "lcnf_nat_to_str" (as := [i64, i64]) (bs := [i64]) (.var rt, .var v0.1, ()) fun v1 =>
    .ret (.var v1.1, ())) m
  refine wp_call_pred (fun (res, ()) m1 =>
    ∃ (st' : BigNumRt.RtC0State) (scrLimbs' : List (BitVec 64)) (objs' : List BigNumRt.LcnfObj),
      st'.PreservesMeta st ∧ st'.rem ≤ st.rem ∧
      mpzAllocBytes 2 + sarrayAllocBytes 40 + strAllocBytes 41 ≤ st'.rem ∧
      BigNumRtWf rt st' scr scrLimbs' ∧ natRep res resVal objs' ∧
      (resVal < 2 ^ 63 → objs' = [] ∧ st'.rem = st.rem) ∧
      (2 ^ 63 ≤ resVal →
        ∃ resObj, resObj ∈ objs' ∧ resObj.addr = res ∧ resObj.rc = 1#32 ∧
          mpzNatCanon resObj resVal ∧ objs'.length ≤ st.workCap ∧
          BigNumRt.lcnfHeapClosed objs' ∧ BigNumRt.RcSound res objs') ∧
      (∀ o ∈ objs', o.Wf) ∧
      (bigNumRtInv rt st' scr scrLimbs' ⋆ BigNumRt.lcnfHeap objs' ⋆ R) m1) ?_ ?_
  · dsimp only [vals, Arg.val, factLoopEnv]; rw [ite_eq_right (by decide)]
    refine Or.inl ⟨⟨rfl, rfl⟩, rfl, st, scr, scrLimbs, [], k, 1, resVal,
      mpzAllocBytes 2 + sarrayAllocBytes 40 + strAllocBytes 41, R, ?_, ?_⟩
    · refine ⟨hkLt, rfl, rfl, hwf, (by simp [natRep]), (fun _ => rfl),
        (fun h => absurd h (by decide)), (fun _ ho => by cases ho),
        (by simp; omega), (by omega), hscrCap, hmaxLimb, (by dsimp only [resVal]; omega),
        sep_cast hm (by simp [BigNumRt.lcnfHeap, sep_emp])⟩
    · intro res st' scrLimbs' objs' m1 hpr1 hrem1 hexRem1 hwf1 hrep1 hsm1 hbig1 hobjsWf1 hm1
      exact ⟨st', scrLimbs', objs', hpr1, hrem1, hexRem1, hwf1, hrep1, hsm1, hbig1, hobjsWf1, hm1⟩
  · rintro ⟨res, ⟨⟩⟩ m1 ⟨st', scrLimbs', objs', hpr1, hrem1, hexRem1, hwf1, hrep1, hsm1, hbig1,
      hobjsWf1, hm1⟩
    refine wp_call_pred Q ?_ fun ⟨s, ⟨⟩⟩ m2 hq => by rw [wp_ret]; exact hq
    dsimp only [vals, Arg.val]
    have hm1_sep :
        (BigNumRt.rtC0Inv rt st' ⋆ BigNumRt.lcnfHeap objs' ⋆
          (cell64 (rt + 33672#64) scr ⋆
            cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs'.length) ⋆
            array64 scr scrLimbs' ⋆ R)) m1 := by
      unfold bigNumRtInv at hm1
      exact sep_cast hm1 (by ac_rfl)
    rcases hcases with hlt63 | htwo
    · rcases hsm1 hlt63 with ⟨rfl, _⟩
      have hresEq : res = boxNat resVal := by
        have hr' := hrep1
        dsimp only [natRep, boxNat] at hr'
        rw [ite_eq_left hlt63] at hr'
        exact hr'
      have hresAnd : res &&& 1#64 ≠ 0#64 := by
        rw [hresEq, boxNat_and_one hlt63]; decide
      have hushr : resVal = (res >>> (1 : Nat)).toNat := by
        have hu : res >>> (1 : Nat) = BitVec.ofNat 64 resVal :=
          hresEq ▸ boxNat_ushr1 hlt63
        rw [hu, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hnil : lcnfHeap ([] : List LcnfObj) = BigNumRt.lcnfHeap [] := by
        rw [b2r_lcnfHeap_eq]; rfl
      have hm1_rt :
          (rtC0Inv rt (b2rState st') ⋆ lcnfHeap ([] : List LcnfObj) ⋆
            (cell64 (rt + 33672#64) scr ⋆
              cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs'.length) ⋆
              array64 scr scrLimbs' ⋆ R)) m1 := by
        rw [← b2r_rtC0Inv_eq, hnil]
        exact hm1_sep
      have hdecLe : (natToDecimalBytes resVal).length ≤ 19 := by
        by_cases hz : resVal = 0
        · unfold natToDecimalBytes; rw [hz, ite_eq_left rfl]; simp
        · unfold natToDecimalBytes
          rw [ite_eq_right hz, List.length_reverse]
          have hpow19 : resVal < 10 ^ 19 := Nat.lt_trans hlt63 (by decide)
          exact natDigitsRev_len_le_of_lt_pow10 19 resVal hpow19
      have hstrRem :
          strAllocBytes ((natToDecimalBytes resVal).length + 1) ≤ (b2rState st').rem := by
        have hle41 :=
          strAllocBytes_mono
            (Nat.le_trans (show (natToDecimalBytes resVal).length + 1 ≤ 20 by omega)
              (by decide : 20 ≤ 41))
        rw [b2rState_rem]
        omega
      have hpr1b : (b2rState st').PreservesMeta (b2rState st) := by
        simpa [BigNumRt.RtC0State.PreservesMeta, RtC0State.PreservesMeta,
          b2rState, b2rHdr] using hpr1
      refine loopRtEnv_le_factLoopEnv_of_mem (by decide) _ _ _ _ _ _
        (rtC0CoreEnv_le_loopRtEnv _ _ _ _ _ _ _
        (rtR2bEnv_le_rtC0CoreEnv _ _ _ _ _ _ _ (rtR2bEnv_lcnf_nat_to_str
          ⟨b2rState st', resVal, [], _,
            (by rw [NatInHeap, ite_eq_left hresAnd]; exact hushr),
            (fun _ ho => by cases ho), hm1_rt, ?_⟩)))
      split
      · refine ⟨Or.inr hstrRem, fun s st2 m2 hs0 hs8 hpr2 hrem2 hcan2 hm2 => ?_⟩
        exact hk s st2 [] scrLimbs' m2 hs0 hs8 (hpr1b.trans hpr2) (Nat.le_trans hrem2 hrem1)
          hcan2 (sep_cast hm2 (by ac_rfl))
      · contradiction
    · have hge63 : 2 ^ 63 ≤ resVal := by
        have hnz : resVal ≠ 0 := by
          dsimp only [resVal] at *; unfold limbLenNat at htwo; split at htwo <;> omega
        have hlog : 1 ≤ resVal.log2 / 64 := by
          dsimp only [resVal] at *; unfold limbLenNat at htwo
          rw [ite_eq_right hnz] at htwo; omega
        have hmod := Nat.div_add_mod resVal.log2 64
        have h64 : 64 ≤ resVal.log2 := by omega
        exact Nat.le_trans (by decide : 2 ^ 63 ≤ 2 ^ 64) ((Nat.le_log2 hnz).mp h64)
      rcases hbig1 hge63 with
        ⟨resObj, hresMem, hresAddr, hresRc, hresCan, hwk1, hcl1, hrc1⟩
      have hresTag : res &&& 1#64 = 0#64 := by
        have hr' := hrep1
        simp only [natRep, Nat.not_lt_of_ge hge63, ↓reduceIte] at hr'
        exact hr'.1
      have hlen2 : resObj.limbs.length = 2 := by
        rw [← mpzNatCanon_limbLen hresCan]; exact htwo
      have hwc' : st'.workCap = st.workCap := preservesMeta_bn_workCap hpr1
      have hpr1b : (b2rState st').PreservesMeta (b2rState st) := by
        simpa [BigNumRt.RtC0State.PreservesMeta, RtC0State.PreservesMeta,
          b2rState, b2rHdr] using hpr1
      refine loopRtEnv_le_factLoopEnv_of_mem (by decide) _ _ _ _ _ _
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨⟨rfl, rfl⟩, rfl, st', resObj, objs', resVal, _, hresTag, hresMem, hresAddr, hresCan, hlen2,
          hobjsWf1, (fun _ => ⟨hwc' ▸ hwk1, hcl1, hrc1⟩), hexRem1, hm1_sep,
          fun s st2 objs2 m2 hs0 hs8 hpr2 hrem2 hcan2 hdec2 hm2 => ?_⟩)))))
      exact hk s st2 objs2 scrLimbs' m2 hs0 hs8 (hpr1b.trans hpr2) (Nat.le_trans hrem2 hrem1)
        hcan2 (sep_cast hm2 (by ac_rfl))

theorem factLoopLinkedMod_wp (fn : Fn) (hfn : fn ∈ factLoopLinkedMod.fns)
    {xs : Tup Val fn.as} {m : Mem 64} {Q : Post fn.rs} {X : XPost}
    (hpre : factLoopEnv fn.name fn.as fn.rs xs m Q X) :
    Func.wp factLoopEnv fn.body xs m Q X := by
  change fn ∈ (linkLcnfWithRtC0 factLoopTfs).fns at hfn
  rw [linkLcnfWithRtC0_fns_eq] at hfn
  rcases List.mem_append.mp hfn with hrt | hprog
  · have hrtIn : fn.name ∈ rtCoreFnNames := by
      simpa [rtCoreFnNames] using List.mem_map_of_mem hrt
    dsimp only [factLoopEnv] at hpre
    rw [ite_eq_left hrtIn] at hpre
    have hloop := rtC0CoreMod_loop_wp hrt hpre
    obtain ⟨pre, post, hsplit⟩ := List.mem_iff_append.mp hrt
    have hmod := rtC0CoreMod_loopModuleOk.fnsOk pre fn post hsplit
    have hwf := hmod.1 Val (fun _ => Unit) Cont (fun _ => Unit) xs (Tup.units fn.as)
    have hcalls := hmod.2.1
    refine wp_env_agree_of_callsOk hwf hcalls ?_ m hloop
    intro g as' bs' hg xs' m' P' E' hp'
    have hmemG : g ∈ rtCoreFnNames := by
      simp only [List.mem_append, List.mem_map] at hg
      rcases hg with ⟨fn', hfn', heq⟩ | ⟨ex, hex, _⟩
      · rw [← (Prod.mk.inj heq).1]
        have hfn'Mem : fn' ∈ rtC0CoreMod.fns := by
          rw [hsplit]; exact List.mem_append_left _ hfn'
        simpa [rtCoreFnNames] using List.mem_map_of_mem hfn'Mem
      · have hnoEx : rtC0CoreMod.externs = [] := rfl
        rw [hnoEx] at hex; contradiction
    exact loopRtEnv_le_factLoopEnv_of_mem hmemG as' bs' xs' m' P' E' hp'
  · have hnd : factLoopLinkedMod.namesNodup :=
      linkLcnfWithRtC0_nodup_of_checkAcyclic (by t_kernel_rfl)
    have hdisj := lcnfProgMod_disjoint_rt_of_nodup hnd fn hprog
    dsimp only [factLoopEnv] at hpre
    rw [ite_eq_right hdisj] at hpre
    have hprogMem : fn ∈ [factLoopTfs.tf_0.toFn, factLoopTfs.tf_1.toFn] := by
      simpa [lcnfProgMod, factLoopTfs, Frontend.C0.tflatFnsToFns] using hprog
    rcases List.mem_cons.mp hprogMem with rfl | hmem1
    · rcases hpre with ⟨⟨has, hrs⟩, _, hsp⟩ | ⟨_, hnm, _⟩
      · cases has; cases hrs; exact factAcc_wp xs m Q X hsp
      · exact absurd hnm (by decide)
    · have hfn1 : fn = factLoopTfs.tf_1.toFn := List.mem_singleton.mp hmem1
      subst hfn1
      rcases hpre with ⟨_, hnm, _⟩ | ⟨⟨has, hrs⟩, _, hsp⟩
      · exact absurd hnm (by decide)
      · cases has; cases hrs; exact factStr_wp xs m Q X hsp

theorem factLoopLinkedMod_fns_wf (fn : Fn) (hfn : fn ∈ factLoopLinkedMod.fns) : fn.Wf :=
  linkLcnfWithRtC0_fns_wf factLoopTfs fn hfn

theorem factLoopLinkedMod_acyclic : factLoopLinkedMod.checkAcyclic = true := by
  t_kernel_rfl

theorem factLoopLinkedMod_moduleOk : ModuleOk factLoopEnv factLoopLinkedMod :=
  Module.moduleOk_of_checkAcyclic factLoopLinkedMod_acyclic factLoopLinkedMod_fns_wf
    (fun fn hfn _ _ _ _ hp => factLoopLinkedMod_wp fn hfn hp)

theorem factLoopEnv_noex (fn : Fn) (hfn : fn ∈ (lcnfProgMod factLoopTfs).fns)
    (args : Tup Val fn.as) (m : Mem 64) (Q : Post fn.rs) (X X' : XPost) :
    factLoopEnv fn.name fn.as fn.rs args m Q X →
      factLoopEnv fn.name fn.as fn.rs args m Q X' := by
  have hnd : factLoopLinkedMod.namesNodup :=
    linkLcnfWithRtC0_nodup_of_checkAcyclic factLoopLinkedMod_acyclic
  have hdisj := lcnfProgMod_disjoint_rt_of_nodup hnd fn hfn
  intro hp
  dsimp only [factLoopEnv] at hp ⊢
  rw [ite_eq_right hdisj] at hp ⊢
  rcases hp with ⟨⟨has, hrs⟩, hnm, hsp⟩ | ⟨⟨has, hrs⟩, hnm, hsp⟩
  · exact Or.inl ⟨⟨has, hrs⟩, hnm, hsp⟩
  · exact Or.inr ⟨⟨has, hrs⟩, hnm, hsp⟩

@[expose] def loopRtBase : BitVec 64 := 1048576#64
@[expose] def loopWorkCap : Nat := 8
@[expose] def loopRem : Nat := 2048
@[expose] def loopScrCap : Nat := 32
@[expose] def loopScr : BitVec 64 := loopRtBase + 35800#64
@[expose] def loopScrLimbs : List (BitVec 64) := List.replicate loopScrCap 0#64

@[expose] def loopRtState : BigNumRt.RtC0State :=
  { extraArgs := List.replicate rtExtraSlots 0#64,
    globals := List.replicate rtGlobalSlots 0#64,
    freeList := List.replicate BigNumRt.rtNumClasses 0#64,
    hdr :=
      { s_large_free := 0#64, s_ba_empty := 0#64,
        s_cur := loopRtBase + 33752#64, s_end := loopRtBase + 35800#64,
        s_work := loopRtBase + 33688#64, s_work_cap := BitVec.ofNat 64 loopWorkCap,
        s_chunks := 0#64, s_nchunks := 0#64, s_chunks_cap := 0#64,
        s_st_allocs := 0#64, s_st_frees := 0#64, s_st_live := 0#64,
        s_st_peak_live := 0#64, s_st_persistent := 0#64, s_st_reused := 0#64,
        s_st_cold_decs := 0#64, s_st_bytes := 0#64 },
    workBuf := List.replicate loopWorkCap 0#64,
    smallPools := fun _ => [],
    largeNodes := [],
    extraLen := List.length_replicate,
    globalsLen := List.length_replicate,
    freeListLen := List.length_replicate,
    workLen := List.length_replicate,
    curLeEnd := by decide,
    arenaAlign := by decide,
    curNz := by decide }

@[expose] def loopRtBytes : List UInt8 :=
  bytes64 loopRtState.extraArgs ++ bytes64 loopRtState.globals ++
    bytes64 loopRtState.freeList ++ bytes64 (nvBnHdrWords loopRtState.hdr) ++
    bytes64 [loopScr, BitVec.ofNat 64 loopScrCap] ++ bytes64 loopRtState.workBuf ++
    List.replicate loopRem 0 ++ bytes64 loopScrLimbs

@[expose] def loopRtMem : Mem 64 := loopRtBytes.At loopRtBase

private theorem sep_of_bytes_append {a : BitVec 64} {bs1 bs2 : List UInt8}
    {P1 P2 : Mem 64 → Prop} {m : Mem 64}
    (h1 : P1 (bs1.At a)) (h2 : P2 (bs2.At (a + BitVec.ofNat 64 bs1.length)))
    (hfit : bs1.length + bs2.length ≤ 2 ^ 64) (hm : bytes a (bs1 ++ bs2) m) :
    (P1 ⋆ P2) m := by
  rw [bytes_append _ _ _ hfit] at hm
  exact sep_mono2 (by rintro _ rfl; exact h1) (by rintro _ rfl; exact h2) m hm

private theorem lcnfC0BaseRt_At_of_bytes64 (p : BitVec 64) (h : LcnfC0BaseRt) :
    LcnfC0BaseRt.At p h ((bytes64 (nvBnHdrWords h)).At (p + 33536#64)) := by
  have ha := array64_bytes (p + 33536#64) (nvBnHdrWords h)
    (by dsimp [nvBnHdrWords]; decide)
  dsimp only [nvBnHdrWords] at ha
  simp only [array64, cell64_eq_cell] at ha
  unfold LcnfC0BaseRt.At
  refine sep_cast ha ?_
  rw [show (8 : BitVec 64) = 8#64 from rfl,
    BitVec.add_assoc p 33536#64 8#64, show (33536#64 + 8#64 : BitVec 64) = 33544#64 from rfl,
    BitVec.add_assoc p 33544#64 8#64, show (33544#64 + 8#64 : BitVec 64) = 33552#64 from rfl,
    BitVec.add_assoc p 33552#64 8#64, show (33552#64 + 8#64 : BitVec 64) = 33560#64 from rfl,
    BitVec.add_assoc p 33560#64 8#64, show (33560#64 + 8#64 : BitVec 64) = 33568#64 from rfl,
    BitVec.add_assoc p 33568#64 8#64, show (33568#64 + 8#64 : BitVec 64) = 33576#64 from rfl,
    BitVec.add_assoc p 33576#64 8#64, show (33576#64 + 8#64 : BitVec 64) = 33584#64 from rfl,
    BitVec.add_assoc p 33584#64 8#64, show (33584#64 + 8#64 : BitVec 64) = 33592#64 from rfl,
    BitVec.add_assoc p 33592#64 8#64, show (33592#64 + 8#64 : BitVec 64) = 33600#64 from rfl,
    BitVec.add_assoc p 33600#64 8#64, show (33600#64 + 8#64 : BitVec 64) = 33608#64 from rfl,
    BitVec.add_assoc p 33608#64 8#64, show (33608#64 + 8#64 : BitVec 64) = 33616#64 from rfl,
    BitVec.add_assoc p 33616#64 8#64, show (33616#64 + 8#64 : BitVec 64) = 33624#64 from rfl,
    BitVec.add_assoc p 33624#64 8#64, show (33624#64 + 8#64 : BitVec 64) = 33632#64 from rfl,
    BitVec.add_assoc p 33632#64 8#64, show (33632#64 + 8#64 : BitVec 64) = 33640#64 from rfl,
    BitVec.add_assoc p 33640#64 8#64, show (33640#64 + 8#64 : BitVec 64) = 33648#64 from rfl,
    BitVec.add_assoc p 33648#64 8#64, show (33648#64 + 8#64 : BitVec 64) = 33656#64 from rfl,
    BitVec.add_assoc p 33656#64 8#64, show (33656#64 + 8#64 : BitVec 64) = 33664#64 from rfl,
    sep_emp]
  ac_rfl

private theorem smallPools_empty_emp (k : Nat) (hk : k ≤ BigNumRt.rtNumClasses) :
    BigNumRt.smallPoolsAt (List.replicate BigNumRt.rtNumClasses 0#64) (fun _ => []) k = emp := by
  induction k with
  | zero => exact BigNumRt.smallPoolsAt.eq_1 _ _
  | succ k ih =>
    rw [BigNumRt.smallPoolsAt.eq_2, ih (Nat.le_of_succ_le hk), emp_sep]
    have hget : (List.replicate BigNumRt.rtNumClasses 0#64).getD k 0#64 = 0#64 := by
      simp [List.getD, Nat.lt_of_succ_le hk]
    rw [hget]
    unfold BigNumRt.smallPoolSlot
    split <;> (ext m; simp [BigNumRt.smallFreeList.eq_1])

private theorem largeFreeList_empty_emp : BigNumRt.largeFreeList 0#64 [] = emp := by
  ext m
  simp [BigNumRt.largeFreeList, BigNumRt.largeSeg.eq_1]

theorem loopRtMem_ok :
    bigNumRtInv loopRtBase loopRtState loopScr loopScrLimbs loopRtMem := by
  have hm0 : bytes loopRtBase loopRtBytes loopRtMem := rfl
  unfold loopRtBytes at hm0
  simp only [List.append_assoc] at hm0
  have ha0 : 8 * loopRtState.extraArgs.length ≤ 2 ^ 64 := by
    rw [loopRtState.extraLen]; decide
  have ha1 : 8 * loopRtState.globals.length ≤ 2 ^ 64 := by
    rw [loopRtState.globalsLen]; decide
  have ha2 : 8 * loopRtState.freeList.length ≤ 2 ^ 64 := by
    rw [loopRtState.freeListLen]; decide
  have ha5 : 8 * loopRtState.workBuf.length ≤ 2 ^ 64 := by
    rw [loopRtState.workLen]; decide
  have ha7 : 8 * loopScrLimbs.length ≤ 2 ^ 64 := by
    rw [show loopScrLimbs.length = loopScrCap from List.length_replicate]; decide
  have hl0 : (bytes64 loopRtState.extraArgs).length = 256 := by
    rw [bytes64_length, loopRtState.extraLen]; rfl
  have hl1 : (bytes64 loopRtState.globals).length = 32768 := by
    rw [bytes64_length, loopRtState.globalsLen]; rfl
  have hl2 : (bytes64 loopRtState.freeList).length = 512 := by
    rw [bytes64_length, loopRtState.freeListLen]; rfl
  have hl3 : (bytes64 (nvBnHdrWords loopRtState.hdr)).length = 136 := by
    rw [bytes64_length]; rfl
  have hl4 : (bytes64 [loopScr, BitVec.ofNat 64 loopScrCap]).length = 16 := by
    rw [bytes64_length]; rfl
  have hl5 : (bytes64 loopRtState.workBuf).length = 64 := by
    rw [bytes64_length, loopRtState.workLen]; rfl
  have hl6 : (List.replicate loopRem (0 : UInt8)).length = 2048 := List.length_replicate
  have hl7 : (bytes64 loopScrLimbs).length = 256 := by
    rw [bytes64_length, show loopScrLimbs.length = loopScrCap from List.length_replicate]; rfl
  let bs7 := List.replicate loopRem (0 : UInt8) ++ bytes64 loopScrLimbs
  let bs6 := bytes64 loopRtState.workBuf ++ bs7
  let bs5 := bytes64 [loopScr, BitVec.ofNat 64 loopScrCap] ++ bs6
  let bs4 := bytes64 (nvBnHdrWords loopRtState.hdr) ++ bs5
  let bs3 := bytes64 loopRtState.freeList ++ bs4
  let bs2 := bytes64 loopRtState.globals ++ bs3
  have hbs7 : bs7.length = 2304 := by simp [bs7, hl6, hl7]
  have hbs6 : bs6.length = 2368 := by simp [bs6, hl5, hbs7]
  have hbs5 : bs5.length = 2384 := by simp [bs5, hl4, hbs6]
  have hbs4 : bs4.length = 2520 := by simp [bs4, hl3, hbs5]
  have hbs3 : bs3.length = 3032 := by simp [bs3, hl2, hbs4]
  have hbs2 : bs2.length = 35800 := by simp [bs2, hl1, hbs3]
  have h7 :
      (region (loopRtBase + 33752#64) loopRem ⋆ array64 loopScr loopScrLimbs)
        (bs7.At (loopRtBase + 33752#64)) := by
    refine sep_of_bytes_append ⟨_, List.length_replicate, rfl⟩ ?_
      (by rw [hl6, hl7]; decide) rfl
    rw [hl6, show (loopRtBase + 33752#64) + BitVec.ofNat 64 2048 = loopScr from rfl]
    exact array64_bytes loopScr loopScrLimbs ha7
  have h6 :
      (array64 (loopRtBase + 33688#64) loopRtState.workBuf ⋆
        (region (loopRtBase + 33752#64) loopRem ⋆ array64 loopScr loopScrLimbs))
        (bs6.At (loopRtBase + 33688#64)) := by
    refine sep_of_bytes_append (array64_bytes _ _ ha5) ?_ (by rw [hl5, hbs7]; decide) rfl
    rw [hl5, show (loopRtBase + 33688#64) + BitVec.ofNat 64 64 =
      loopRtBase + 33752#64 from rfl]
    exact h7
  have h5 :
      (cell64 (loopRtBase + 33672#64) loopScr ⋆
        cell64 (loopRtBase + 33680#64) (BitVec.ofNat 64 loopScrCap) ⋆
        array64 (loopRtBase + 33688#64) loopRtState.workBuf ⋆
        region (loopRtBase + 33752#64) loopRem ⋆ array64 loopScr loopScrLimbs)
        (bs5.At (loopRtBase + 33672#64)) := by
    have hs :
        (array64 (loopRtBase + 33672#64) [loopScr, BitVec.ofNat 64 loopScrCap] ⋆
          (array64 (loopRtBase + 33688#64) loopRtState.workBuf ⋆
            (region (loopRtBase + 33752#64) loopRem ⋆ array64 loopScr loopScrLimbs)))
          (bs5.At (loopRtBase + 33672#64)) := by
      refine sep_of_bytes_append (array64_bytes _ _ (by decide)) ?_
        (by rw [hl4, hbs6]; decide) rfl
      rw [hl4, show (loopRtBase + 33672#64) + BitVec.ofNat 64 16 =
        loopRtBase + 33688#64 from rfl]
      exact h6
    simp only [array64, sep_emp,
      show (loopRtBase + 33672#64) + 8 = loopRtBase + 33680#64 from rfl] at hs
    exact sep_cast hs (by ac_rfl)
  have h4 :
      (LcnfC0BaseRt.At loopRtBase loopRtState.hdr ⋆
        (cell64 (loopRtBase + 33672#64) loopScr ⋆
          cell64 (loopRtBase + 33680#64) (BitVec.ofNat 64 loopScrCap) ⋆
          array64 (loopRtBase + 33688#64) loopRtState.workBuf ⋆
          region (loopRtBase + 33752#64) loopRem ⋆ array64 loopScr loopScrLimbs))
        (bs4.At (loopRtBase + 33536#64)) := by
    refine sep_of_bytes_append (lcnfC0BaseRt_At_of_bytes64 loopRtBase loopRtState.hdr) ?_
      (by rw [hl3, hbs5]; decide) rfl
    rw [hl3, show (loopRtBase + 33536#64) + BitVec.ofNat 64 136 =
      loopRtBase + 33672#64 from rfl]
    exact h5
  have h3 :
      (array64 (loopRtBase + 33024#64) loopRtState.freeList ⋆
        (LcnfC0BaseRt.At loopRtBase loopRtState.hdr ⋆
          (cell64 (loopRtBase + 33672#64) loopScr ⋆
            cell64 (loopRtBase + 33680#64) (BitVec.ofNat 64 loopScrCap) ⋆
            array64 (loopRtBase + 33688#64) loopRtState.workBuf ⋆
            region (loopRtBase + 33752#64) loopRem ⋆ array64 loopScr loopScrLimbs)))
        (bs3.At (loopRtBase + 33024#64)) := by
    refine sep_of_bytes_append (array64_bytes _ _ ha2) ?_ (by rw [hl2, hbs4]; decide) rfl
    rw [hl2, show (loopRtBase + 33024#64) + BitVec.ofNat 64 512 =
      loopRtBase + 33536#64 from rfl]
    exact h4
  have h2 :
      (array64 (loopRtBase + 256#64) loopRtState.globals ⋆
        (array64 (loopRtBase + 33024#64) loopRtState.freeList ⋆
          (LcnfC0BaseRt.At loopRtBase loopRtState.hdr ⋆
            (cell64 (loopRtBase + 33672#64) loopScr ⋆
              cell64 (loopRtBase + 33680#64) (BitVec.ofNat 64 loopScrCap) ⋆
              array64 (loopRtBase + 33688#64) loopRtState.workBuf ⋆
              region (loopRtBase + 33752#64) loopRem ⋆ array64 loopScr loopScrLimbs))))
        (bs2.At (loopRtBase + 256#64)) := by
    refine sep_of_bytes_append (array64_bytes _ _ ha1) ?_ (by rw [hl1, hbs3]; decide) rfl
    rw [hl1, show (loopRtBase + 256#64) + BitVec.ofNat 64 32768 =
      loopRtBase + 33024#64 from rfl]
    exact h3
  have h1 :
      (array64 loopRtBase loopRtState.extraArgs ⋆
        (array64 (loopRtBase + 256#64) loopRtState.globals ⋆
          (array64 (loopRtBase + 33024#64) loopRtState.freeList ⋆
            (LcnfC0BaseRt.At loopRtBase loopRtState.hdr ⋆
              (cell64 (loopRtBase + 33672#64) loopScr ⋆
                cell64 (loopRtBase + 33680#64) (BitVec.ofNat 64 loopScrCap) ⋆
                array64 (loopRtBase + 33688#64) loopRtState.workBuf ⋆
                region (loopRtBase + 33752#64) loopRem ⋆ array64 loopScr loopScrLimbs)))))
        loopRtMem :=
    sep_of_bytes_append (array64_bytes loopRtBase loopRtState.extraArgs ha0)
      (by rw [hl0]; exact h2) (by rw [hl0, hbs2]; decide) hm0
  unfold bigNumRtInv BigNumRt.rtC0Inv
  have hsp :
      BigNumRt.smallPoolsAt loopRtState.freeList loopRtState.smallPools BigNumRt.rtNumClasses =
        emp :=
    smallPools_empty_emp _ (Nat.le_refl _)
  have hlf : BigNumRt.largeFreeList loopRtState.hdr.s_large_free loopRtState.largeNodes = emp :=
    largeFreeList_empty_emp
  rw [hsp, hlf]
  change (array64 loopRtBase loopRtState.extraArgs ⋆
    array64 (loopRtBase + 256#64) loopRtState.globals ⋆
    array64 (loopRtBase + 33024#64) loopRtState.freeList ⋆
    LcnfC0BaseRt.At loopRtBase loopRtState.hdr ⋆
    array64 (loopRtBase + 33688#64) loopRtState.workBuf ⋆ emp ⋆ emp ⋆
    region (loopRtBase + 33752#64) loopRem ⋆
    cell64 (loopRtBase + 33672#64) loopScr ⋆
    cell64 (loopRtBase + 33680#64) (BitVec.ofNat 64 loopScrLimbs.length) ⋆
    array64 loopScr loopScrLimbs) loopRtMem
  exact sep_cast h1 (by simp only [sep_emp]; ac_rfl)

theorem fact25_str_spec (Q : Post [i64]) (X : XPost)
    (hk : ∀ (s : BitVec 64) (st' : RtC0State) (objs' : List LcnfObj)
      (scrLimbs' : List (BitVec 64)) (m' : Mem 64),
      s ≠ 0#64 → s.toNat % 8 = 0 →
      st'.PreservesMeta (b2rState loopRtState) → st'.rem ≤ loopRtState.rem →
      have sObj := mkStrObj s 1#32 27 fact25Bytes 26
      StrCanon sObj →
      (rtC0Inv loopRtBase st' ⋆ lcnfObjMem sObj ⋆ lcnfHeap objs' ⋆
        cell64 (loopRtBase + 33672#64) loopScr ⋆
        cell64 (loopRtBase + 33680#64) (BitVec.ofNat 64 scrLimbs'.length) ⋆
        array64 loopScr scrLimbs') m' →
      Q (s, ()) m') :
    factLoopEnv "l_LeanQbe_T_LeanLCNF_FactLoop_factStr" [i64, i64] [i64]
      (loopRtBase, boxNat 25, ()) loopRtMem Q X := by
  dsimp only [factLoopEnv]
  rw [ite_eq_right (by decide)]
  have hlog : limbLenNat (FactLoop.factAcc 25 1) = 2 := by
    rw [fact25_acc_eq]
    unfold limbLenNat
    rw [ite_eq_right (by decide : (15511210043330985984000000 : Nat) ≠ 0)]
    have hlo : 64 ≤ Nat.log2 15511210043330985984000000 :=
      (Nat.le_log2 (by decide)).mpr (by decide)
    have hhi : Nat.log2 15511210043330985984000000 < 128 :=
      (Nat.log2_lt (by decide)).mpr (by decide)
    omega
  have hwf1 : loopRtState.Bounded48 := by unfold BigNumRt.RtC0State.Bounded48; decide
  have hwf2 : loopRtBase.toNat + LcnfC0BigNumRt.sizeof < 2 ^ 64 := by decide
  have hwf3 : loopScr ≠ 0#64 := by decide
  have hwf4 : loopScr.toNat % 8 = 0 := by decide
  have hwf5 : loopScrLimbs.length < 2 ^ 64 := by
    rw [show loopScrLimbs.length = loopScrCap from List.length_replicate]; decide
  have hwf6 : loopScr.toNat + 8 * loopScrLimbs.length < 2 ^ 64 := by
    rw [show loopScrLimbs.length = loopScrCap from List.length_replicate]; decide
  have hwf : BigNumRtWf loopRtBase loopRtState loopScr loopScrLimbs :=
    ⟨hwf1, hwf2, hwf3, hwf4, hwf5, hwf6⟩
  refine Or.inr ⟨⟨rfl, rfl⟩, rfl, loopRtState, loopScr, loopScrLimbs, 25, emp,
    by decide, rfl, hwf,
    by dsimp [BigNumRt.RtC0State.workCap, loopRtState, loopWorkCap]; decide,
    by simp [hlog, loopScrLimbs, loopScrCap],
    by rw [hlog]; decide, Or.inr hlog,
    by simp [hlog, mpzAllocBytes, sarrayAllocBytes, strAllocBytes, align8,
      loopRtState, BigNumRt.RtC0State.rem]; decide,
    by rw [sep_emp]; exact loopRtMem_ok, ?_⟩
  intro s st' objs' scrLimbs' m' hs0 hs8 hpr hrem dec sObj hcan hm'
  dsimp only [dec, sObj] at hcan hm'
  rw [fact25_dec, fact25Bytes_len] at hcan hm'
  exact hk s st' objs' scrLimbs' m' hs0 hs8 hpr hrem hcan (sep_cast hm' (by simp [sep_emp]))

end LeanQbe.T.LeanLCNF
