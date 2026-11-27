module
public import LeanQbe.T.LeanLCNF.LcnfC0LoopDemo
public import LeanQbe.T.LeanLCNF.LcnfC0FullProof
public import LeanQbe.T.LeanLCNF.LcnfC0BigNumProof1
public import LeanQbe.T.LeanLCNF.LcnfC0BigNumProof4
public import LeanQbe.T.LeanLCNF.LcnfC0BigNumProof5
public import LeanQbe.T.LeanLCNF.LcnfC0RtProofNv
public import LeanQbe.T.LeanLCNF.LcnfC0StringsSpec
public import LeanQbe.T.LeanLCNF.LcnfC0StringsProof1
public import LeanQbe.T.Logic.C0HeadStep
public import LeanQbe.T.Logic.ControlComb
public import LeanQbe.T.Logic.ProofKit
/-!
# Dual-Arch WP Proof for `FactLoop` (`LcnfC0LoopDemoProof`)
Verifies the lowered Lean `LCNF` self-tail factorial loop `FactLoop.factAcc` and decimal
formatter `FactLoop.factStr` against a strengthened `rtC0CoreMod` environment `loopRtEnv`
with zero edits to `Core`, `Kissat`, `Bootstrap0`, or `LcnfC0FullCert*`.
-/
set_option autoImplicit false
public section
namespace LeanQbe.T.LeanLCNF
open LeanQbe.T LeanQbe.T.Frontend.C0 LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open Std Std.ExtHashMap
open scoped LeanQbe.T.ProofUtil
/-! ## 1. Meta-Preservation, Header-Load, and RC Helpers -/
theorem preservesMeta_bn_s_end {st' st : RtC0State}
    (h : st'.PreservesMeta st) : st'.hdr.s_end = st.hdr.s_end := h.2.2.2.1.symm
theorem preservesMeta_bn_workCap {st' st : RtC0State}
    (h : st'.PreservesMeta st) : st'.workCap = st.workCap := by
  simp only [RtC0State.workCap, RtC0State.PreservesMeta] at h ⊢
  rw [h.2.2.2.2.2.1]
theorem preservesMeta_bn_bounded48 {st' st : RtC0State}
    (hb : st.Bounded48) (h : st'.PreservesMeta st) : st'.Bounded48 := by
  simpa [RtC0State.Bounded48, preservesMeta_bn_s_end h] using hb
theorem preservesMeta_bn_trans {a b c : RtC0State}
    (h1 : b.PreservesMeta a) (h2 : c.PreservesMeta b) : c.PreservesMeta a := by
  rcases h1 with ⟨h11, h12, h13, h14, h15, h16, h17, h18, h19⟩
  rcases h2 with ⟨h21, h22, h23, h24, h25, h26, h27, h28, h29⟩
  exact ⟨h11.trans h21, h12.trans h22, h13.trans h23, h14.trans h24, h15.trans h25,
    h16.trans h26, h17.trans h27, h18.trans h28, h19.trans h29⟩
private theorem toBytes_8_take_4 (z : Int) : (Int.toBytes 8 z).take 4 = Int.toBytes 4 z := rfl
private theorem header_setWidth_32 (o : LcnfObj) : o.header.setWidth 32 = o.rc := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_setWidth, LcnfObj.header]
  have hi32 : ¬ (32 ≤ i) := by omega
  have hi48 : ¬ (48 ≤ i) := by omega
  have hi56 : ¬ (56 ≤ i) := by omega
  have hmod : i < 32 := hi
  have h64 : i < 64 := by omega
  simp only [Nat.testBit_mod_two_pow, hmod, decide_true, Bool.true_and]
  have hlor : ∀ (a b : BitVec 64), (a ||| b).toNat.testBit i =
      (a.toNat.testBit i || b.toNat.testBit i) := fun a b => by
    rw [BitVec.toNat_or, Nat.testBit_or]
  rw [hlor, hlor, hlor]
  have hshl : ∀ (x k : Nat), k ≥ 32 → (BitVec.ofNat 64 x <<< k).toNat.testBit i = false := by
    intro x k hk
    rw [BitVec.toNat_shiftLeft, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft]
    have hlt : ¬ (k ≤ i) := by omega
    simp [hlt]
  rw [hshl _ 32 (by decide), hshl _ 48 (by decide), hshl _ 56 (by decide)]
  have hrc64 : o.rc.toNat % 2 ^ 64 = o.rc.toNat :=
    Nat.mod_eq_of_lt (Nat.lt_trans o.rc.isLt (by decide))
  simp only [Bool.or_false, BitVec.toNat_ofNat, hrc64]
theorem loadVal_i32_cell64_header {o : LcnfObj} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (cell64 o.addr o.header ⋆ R) m) : loadVal m i32 o.addr = some o.rc := by
  have hsep : cell64 o.addr o.header =
      (Eq ((Int.toBytes 4 o.header.toInt).At o.addr) ⋆
        Eq (((Int.toBytes 8 o.header.toInt).drop 4).At (o.addr + 4#64))) := by
    unfold cell64
    conv => lhs; rw [← List.take_append_drop 4 (Int.toBytes 8 o.header.toInt), toBytes_8_take_4]
    exact Mem.At_append_sep (Int.toBytes 4 o.header.toInt)
      ((Int.toBytes 8 o.header.toInt).drop 4) o.addr (by simp [Int.toBytes_length])
  rw [hsep, sep_assoc] at hm
  have hload := loadVal_toBytes_bits (n := 32) (by decide) hm
  have hrc : BitVec.ofInt 32 o.header.toInt = o.rc := by
    rw [← header_setWidth_32 o]
    apply BitVec.eq_of_toNat_eq
    have hto : o.header.toInt % (2 : Int) ^ 64 = (o.header.toNat : Int) := by
      simp only [BitVec.toInt_eq_msb_cond]
      split <;> omega
    have hdvd : ((2 : Int) ^ 32) ∣ ((2 : Int) ^ 64) := ⟨2 ^ 32, by decide⟩
    have hmod : o.header.toInt % (2 : Int) ^ 32 = ((o.header.toNat % 2 ^ 32 : Nat) : Int) := by
      rw [← Int.emod_emod_of_dvd o.header.toInt hdvd, hto]
      omega
    have hmod' :
        o.header.toInt % ((2 ^ 32 : Nat) : Int) = ((o.header.toNat % 2 ^ 32 : Nat) : Int) := by
      simpa using hmod
    simp only [BitVec.toNat_ofInt, BitVec.toNat_setWidth, hmod', Int.toNat_natCast]
  rwa [hrc] at hload
private theorem bn_nonPersistRefs_foldl_add (objs : List LcnfObj) (addr : BitVec 64)
    (init : Nat) :
    List.foldl (fun acc p => if p.rc = 0#32 then acc else acc + List.count addr p.childFields)
      init objs = init + nonPersistRefs objs addr := by
  change List.foldl _ init objs = init + List.foldl _ 0 objs
  induction objs generalizing init with
  | nil => simp
  | cons o os ih =>
    simp only [List.foldl_cons, Nat.zero_add]
    by_cases hrc : o.rc = 0#32
    · simp only [hrc, ↓reduceIte]
      exact ih init
    · simp only [hrc, ↓reduceIte]
      rw [ih (init + List.count addr o.childFields), ih (List.count addr o.childFields)]
      omega
theorem bn_nonPersistRefs_cons (o : LcnfObj) (os : List LcnfObj)
    (addr : BitVec 64) :
    nonPersistRefs (o :: os) addr =
      (if o.rc = 0#32 then 0 else List.count addr o.childFields) +
        nonPersistRefs os addr := by
  unfold nonPersistRefs
  simp only [List.foldl_cons, Nat.zero_add]
  by_cases hrc : o.rc = 0#32
  · simp [hrc]
  · simp only [hrc, ↓reduceIte]
    exact bn_nonPersistRefs_foldl_add os addr _
theorem mpz_childFields_nil {o : LcnfObj} (htag : o.tag = mpzTag) :
    o.childFields = [] := by
  simp [LcnfObj.childFields, htag, mpzTag, closureTag, arrayTag]
theorem nonPersistRefs_eq_zero_of_not_child (objs : List LcnfObj) (addr : BitVec 64)
    (hnone : ∀ o ∈ objs, addr ∉ o.childFields) :
    nonPersistRefs objs addr = 0 := by
  induction objs with
  | nil => rfl
  | cons o os ih =>
    rw [bn_nonPersistRefs_cons, ih (fun x hx => hnone x (List.mem_cons_of_mem _ hx))]
    have hcnt : List.count addr o.childFields = 0 :=
      List.count_eq_zero.mpr (hnone o List.mem_cons_self)
    split <;> simp [hcnt]
theorem nonPersistRefs_eq_zero_of_fresh {objs : List LcnfObj} {addr : BitVec 64}
    (halign : addr &&& 1#64 = 0#64) (hcl : lcnfHeapClosed objs)
    (hfresh : addr ∉ objs.map LcnfObj.addr) :
    nonPersistRefs objs addr = 0 := by
  refine nonPersistRefs_eq_zero_of_not_child objs addr ?_
  intro o ho hmem
  obtain ⟨q, hq, hqa⟩ := hcl o ho addr hmem halign
  exact hfresh (List.mem_map.mpr ⟨q, hq, hqa⟩)
private theorem nodup_addr_eq {objs : List LcnfObj}
    (hnodup : (objs.map LcnfObj.addr).Nodup) {x y : LcnfObj}
    (hx : x ∈ objs) (hy : y ∈ objs) (haddr : x.addr = y.addr) : x = y := by
  induction objs with
  | nil => cases hx
  | cons z zs ih =>
    simp only [List.map_cons, List.nodup_cons] at hnodup
    rcases List.mem_cons.mp hx with rfl | hx'
    · rcases List.mem_cons.mp hy with rfl | hy'
      · rfl
      · exfalso; exact hnodup.1 (haddr ▸ List.mem_map_of_mem hy')
    · rcases List.mem_cons.mp hy with rfl | hy'
      · exfalso; exact hnodup.1 (haddr.symm ▸ List.mem_map_of_mem hx')
      · exact ih hnodup.2 hx' hy'
theorem nonPersistReach_mpz_eq {objs : List LcnfObj}
    (hnodup : (objs.map LcnfObj.addr).Nodup)
    {accObj : LcnfObj} (hacc : accObj ∈ objs) (htag : accObj.tag = mpzTag)
    {v : BitVec 64} (hreach : NonPersistReach objs accObj.addr v) :
    v = accObj.addr := by
  induction hreach with
  | refl => rfl
  | @step u w hru hchild _ _ ih =>
    subst ih
    rcases hchild with ⟨o, ho, huo, hw⟩
    have heq : o = accObj := nodup_addr_eq hnodup ho hacc huo
    subst heq
    rw [mpz_childFields_nil htag] at hw
    cases hw
theorem list_getLast_eq_getLast! {α : Type} [Inhabited α] (xs : List α)
    (hne : xs ≠ []) : xs.getLast hne = xs.getLast! := by
  cases xs with
  | nil => exact absurd rfl hne
  | cons x xs => simp [List.getLast!]
theorem mpzNatCanon_limbLen {o : LcnfObj} {val : Nat} (hc : mpzNatCanon o val) :
    limbLenNat val = o.limbs.length := by
  rcases hc with ⟨_, _, _, _, hlen1, _, hlast, hval, hge⟩
  have hne : o.limbs ≠ [] := List.ne_nil_of_length_pos hlen1
  have hlow : 2 ^ (64 * (o.limbs.length - 1)) ≤ val := by
    rw [← hval]
    exact limbsVal_ge_pow_of_nonzero_last hne
      (by rwa [list_getLast_eq_getLast! o.limbs hne])
  have hhi : val < 2 ^ (64 * o.limbs.length) := by
    rw [← hval]
    exact limbsVal_lt_pow o.limbs
  have hpos : val ≠ 0 := by
    have hp : 0 < 2 ^ 63 := by decide
    omega
  simp only [limbLenNat, hpos, ↓reduceIte]
  have hlog_lo : 64 * (o.limbs.length - 1) ≤ val.log2 := (Nat.le_log2 hpos).mpr hlow
  have hlog_hi : val.log2 < 64 * o.limbs.length := (Nat.log2_lt hpos).mpr hhi
  omega
theorem natRep_limbLen_le {w : BitVec 64} {val : Nat} {objs : List LcnfObj}
    (hr : natRep w val objs) : limbLenNat val ≤ mpzMaxLimbs := by
  by_cases hlt : val < 2 ^ 63
  · by_cases hv0 : val = 0
    · simp [limbLenNat, hv0]
    · have hlog : val.log2 < 63 := (Nat.log2_lt hv0).mpr hlt
      simp only [limbLenNat, hv0, ↓reduceIte]
      have hdiv : val.log2 / 64 = 0 := Nat.div_eq_of_lt (by omega)
      rw [hdiv]
      decide
  · simp only [natRep, hlt, ↓reduceIte] at hr
    rcases hr with ⟨_, obj, _, _, hc⟩
    rw [mpzNatCanon_limbLen hc]
    exact hc.2.2.2.2.2.1
private theorem nat_log2_mono {a b : Nat} (h : a ≤ b) : a.log2 ≤ b.log2 := by
  by_cases ha : a = 0
  · subst ha; simp
  · have hb : b ≠ 0 := by omega
    refine Classical.byContradiction fun hlt => ?_
    have hlt' : b.log2 + 1 ≤ a.log2 := by omega
    have h1 : 2 ^ a.log2 ≤ a := (Nat.le_log2 ha).mp (Nat.le_refl _)
    have h2 : b < 2 ^ (b.log2 + 1) := (Nat.log2_lt hb).mp (Nat.lt_succ_self _)
    have h3 : 2 ^ (b.log2 + 1) ≤ 2 ^ a.log2 := Nat.pow_le_pow_right (by decide) hlt'
    omega
theorem limbLenNat_mono_le {a b : Nat} (h : a ≤ b) : limbLenNat a ≤ limbLenNat b := by
  by_cases ha : a = 0
  · subst ha; simp [limbLenNat]
  · have hb : b ≠ 0 := by omega
    simp only [limbLenNat, ha, hb, ↓reduceIte]
    exact Nat.add_le_add_right (Nat.div_le_div_right (nat_log2_mono h)) 1
theorem lcnfHeapClosed_cons_mpz {objs : List LcnfObj} {newObj : LcnfObj}
    (htag : newObj.tag = mpzTag) (hcl : lcnfHeapClosed objs) :
    lcnfHeapClosed (newObj :: objs) := by
  intro o ho f hf hbit
  rcases List.mem_cons.mp ho with rfl | ho'
  · rw [mpz_childFields_nil htag] at hf; cases hf
  · obtain ⟨q, hq, hqa⟩ := hcl o ho' f hf hbit
    exact ⟨q, List.mem_cons_of_mem _ hq, hqa⟩
theorem rcSound_cons_mpz {root : BitVec 64} {objs : List LcnfObj}
    {newObj : LcnfObj} (htag : newObj.tag = mpzTag) (hrc : newObj.rc = 1#32)
    (halign : newObj.addr &&& 1#64 = 0#64)
    (hfresh : newObj.addr ∉ objs.map LcnfObj.addr)
    (hne : newObj.addr ≠ root) (hcl : lcnfHeapClosed objs)
    (hsound : RcSound root objs) :
    RcSound root (newObj :: objs) := by
  refine ⟨?_, ?_⟩
  · intro p hp hp0 f hf hbit
    rcases List.mem_cons.mp hp with rfl | hp'
    · simp [hrc] at hp0
    · obtain ⟨q, hq, hqa, hqrc⟩ := hsound.1 p hp' hp0 f hf hbit
      exact ⟨q, List.mem_cons_of_mem _ hq, hqa, hqrc⟩
  · intro y hy hypos
    rcases List.mem_cons.mp hy with rfl | hy'
    · rw [bn_nonPersistRefs_cons, mpz_childFields_nil htag,
        nonPersistRefs_eq_zero_of_fresh halign hcl hfresh]
      simp [hrc, hne]
    · rw [bn_nonPersistRefs_cons, mpz_childFields_nil htag]
      have hcnt : List.count y.addr ([] : List (BitVec 64)) = 0 := by simp
      simp only [hcnt]
      split
      · simpa using hsound.2 y hy' hypos
      · simpa using hsound.2 y hy' hypos
theorem rcSound_singleton_mpz {newObj : LcnfObj}
    (htag : newObj.tag = mpzTag) (hrc : newObj.rc = 1#32) :
    RcSound newObj.addr [newObj] := by
  refine ⟨?_, ?_⟩
  · intro p hp hp0
    rcases List.mem_cons.mp hp with rfl | hp'
    · simp [hrc] at hp0
    · cases hp'
  · intro y hy _
    rcases List.mem_cons.mp hy with rfl | hy'
    · rw [bn_nonPersistRefs_cons, mpz_childFields_nil htag]
      simp [hrc, nonPersistRefs]
    · cases hy'
private theorem lcnfObj_eq_of_fields {a b : LcnfObj}
    (h1 : a.addr = b.addr) (h2 : a.rc = b.rc) (h3 : a.csSz = b.csSz) (h4 : a.other = b.other)
    (h5 : a.tag = b.tag) (h6 : a.funId = b.funId) (h7 : a.arity = b.arity) (h8 : a.cap = b.cap)
    (h9 : a.arrSize = b.arrSize) (h10 : a.strLen = b.strLen) (h11 : a.fields = b.fields)
    (h12 : a.scalarData = b.scalarData) (h13 : a.limbs = b.limbs) : a = b := by
  cases a; cases b
  simp only at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  rfl
theorem decColdRel_mpz_step {objs objs' : List LcnfObj}
    {newObj accObj : LcnfObj} {R : Mem 64 → Prop} {m m' : Mem 64}
    (hm : (lcnfHeap (newObj :: objs) ⋆ R) m)
    (hnt : newObj.tag = mpzTag) (hnrc : newObj.rc = 1#32)
    (hacc : accObj ∈ objs) (hat : accObj.tag = mpzTag)
    (hcl : lcnfHeapClosed objs)
    (hdec : DecColdRel accObj.addr (newObj :: objs) objs')
    (hm' : (lcnfHeap objs' ⋆ R) m') :
    newObj ∈ objs' ∧
    objs'.length ≤ objs.length ∧
    (∀ o ∈ objs', o.Wf) ∧
    lcnfHeapClosed objs' ∧
    RcSound newObj.addr objs' := by
  have hnodup : ((newObj :: objs).map LcnfObj.addr).Nodup :=
    lcnfHeap_nodup_addrs hm
  have hnodup' : (objs'.map LcnfObj.addr).Nodup :=
    lcnfHeap_nodup_addrs hm'
  have hfresh : newObj.addr ∉ objs.map LcnfObj.addr := by
    simp only [List.map_cons, List.nodup_cons] at hnodup
    exact hnodup.1
  have hne : newObj.addr ≠ accObj.addr :=
    fun heq => hfresh (heq ▸ List.mem_map_of_mem hacc)
  rcases hdec with ⟨_, _, _, hcl', hall', hzero', hpos', _, hdrop⟩
  have hnew_in_addr : newObj.addr ∈ objs'.map LcnfObj.addr := by
    refine Classical.byContradiction fun hmiss => ?_
    have hfreed : newObj ∈ freedObjs (newObj :: objs) objs' := by
      simp only [freedObjs, List.mem_filter, List.mem_cons, true_or, true_and,
        Bool.not_eq_true']
      exact decide_eq_false (fun hc => hmiss (List.contains_iff_mem.mp hc))
    have hreach := ((hdrop newObj List.mem_cons_self (by simp [hnrc])).2 hfreed).2
    have heq := nonPersistReach_mpz_eq hnodup (List.mem_cons_of_mem _ hacc) hat hreach
    exact hne heq
  rcases List.mem_map.mp hnew_in_addr with ⟨newObj', hnew', hnew_addr⟩
  have hnew'_spec := hall' newObj' hnew'
  rcases hnew'_spec.2.2 with
    ⟨o0, ho0, haddr0, hcs, hot, htg, hfn, har, hcp, hars, hsl, hfl, hsc, hlm, hrc0⟩
  have ho0_eq : o0 = newObj :=
    nodup_addr_eq hnodup ho0 List.mem_cons_self (haddr0.trans hnew_addr)
  rw [ho0_eq] at hcs hot htg hfn har hcp hars hsl hfl hsc hlm hrc0
  have hdrop_new :=
    (hdrop newObj List.mem_cons_self (by simp [hnrc])).1 newObj' hnew' hnew_addr
  have hrcpos' : 0 < newObj'.rc.toInt := by
    rcases hrc0 with ⟨h0, _⟩ | ⟨_, hpos, _⟩
    · simp [hnrc] at h0
    · exact hpos
  have hrc1_nat : newObj'.rc.toNat = 1 := by
    have hge1 : 1 ≤ newObj'.rc.toNat := by
      have hlt : newObj'.rc.toNat < 2 ^ 32 := newObj'.rc.isLt
      simp only [BitVec.toInt_eq_msb_cond] at hrcpos'
      split at hrcpos' <;> omega
    have htonat : newObj.rc.toNat = 1 := by simp [hnrc]
    omega
  have hrc_eq : newObj'.rc = newObj.rc := by
    rw [hnrc]
    exact BitVec.eq_of_toNat_eq hrc1_nat
  have hnew'_eq : newObj' = newObj :=
    lcnfObj_eq_of_fields hnew_addr hrc_eq hcs hot htg hfn har hcp hars hsl hfl hsc hlm
  have hmem_new : newObj ∈ objs' := hnew'_eq ▸ hnew'
  have hlen : objs'.length ≤ objs.length := by
    have hsub3 : ∀ a ∈ objs'.map LcnfObj.addr,
        a ∈ (newObj.addr :: (objs.map LcnfObj.addr).erase accObj.addr) := by
      intro a ha
      rcases List.mem_map.mp ha with ⟨x, hx, rfl⟩
      have hx_spec := hall' x hx
      have hne_acc : x.addr ≠ accObj.addr := hx_spec.2.1
      rcases hx_spec.2.2 with ⟨ox, hox, hox_addr, _⟩
      rcases List.mem_cons.mp hox with rfl | hox'
      · exact hox_addr ▸ List.mem_cons_self
      · apply List.mem_cons_of_mem
        rw [← hox_addr]
        exact (List.mem_erase_of_ne (by simpa [hox_addr] using hne_acc)).mpr
          (List.mem_map_of_mem hox')
    have hlen_sub : ∀ {l1 l2 : List (BitVec 64)}, l1.Nodup → (∀ a ∈ l1, a ∈ l2) →
        l1.length ≤ l2.length := by
      intro l1 l2 hn1 hsubl
      induction l1 generalizing l2 with
      | nil => simp
      | cons b bs ihb =>
        simp only [List.nodup_cons] at hn1
        have hb2 : b ∈ l2 := hsubl b List.mem_cons_self
        have ihs := ihb (l2 := l2.erase b) hn1.2 (fun z hz =>
          (List.mem_erase_of_ne (fun hzb => hn1.1 (by subst hzb; exact hz))).mpr
            (hsubl z (List.mem_cons_of_mem _ hz)))
        have hle : (l2.erase b).length + 1 = l2.length := by
          rw [List.length_erase_of_mem hb2]
          have hpos : 0 < l2.length := List.length_pos_of_mem hb2
          omega
        simp only [List.length_cons]; omega
    have hcard := hlen_sub hnodup' hsub3
    have her : ((objs.map LcnfObj.addr).erase accObj.addr).length + 1 = objs.length := by
      rw [List.length_erase_of_mem (List.mem_map_of_mem hacc), List.length_map]
      have hpos : 0 < objs.length := List.length_pos_of_mem hacc
      omega
    simp only [List.length_map, List.length_cons] at hcard
    omega
  refine ⟨hmem_new, hlen, fun o ho => (hall' o ho).1, hcl', ?_⟩
  refine ⟨hzero', fun y hy hypos => ?_⟩
  by_cases hy_new : y.addr = newObj.addr
  · have hy_eq : y = newObj := nodup_addr_eq hnodup' hy hmem_new hy_new
    subst y
    have hnone : ∀ x ∈ objs', newObj.addr ∉ x.childFields := by
      intro x hx hmem
      have hxc := (hall' x hx).2.2
      rcases hxc with ⟨ox, hox, _, _, _, hxtag, _, _, _, _, _, hxfields, _⟩
      have hcf_eq : x.childFields = ox.childFields := by
        simp [LcnfObj.childFields, hxtag, hxfields]
      rw [hcf_eq] at hmem
      rcases List.mem_cons.mp hox with rfl | hox'
      · rw [mpz_childFields_nil hnt] at hmem; cases hmem
      · have h0_align : newObj.addr &&& 1#64 = 0#64 := by
          rcases (hall' newObj hmem_new).1 with ⟨_, hmod, _⟩
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_and, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by decide : 1 < 2 ^ 64),
            Nat.and_one_is_mod]
          omega
        obtain ⟨q, hq, hqa⟩ := hcl ox hox' newObj.addr hmem h0_align
        exact hfresh (hqa ▸ List.mem_map_of_mem hq)
    rw [nonPersistRefs_eq_zero_of_not_child objs' newObj.addr hnone]
    simp [hnrc]
  · simp only [hy_new, ↓reduceIte, Nat.add_zero]
    exact hpos' y hy hypos

end LeanQbe.T.LeanLCNF
