module

public import LeanQbe.T.LeanLCNF.LcnfC0Strings
public import LeanQbe.T.LeanLCNF.LcnfC0StringsSpec
public import LeanQbe.T.LeanLCNF.LcnfC0StringsProof1
public import LeanQbe.T.LeanLCNF.LcnfC0StringsProof2
public import LeanQbe.T.LeanLCNF.LcnfC0ContainersProof1
public import LeanQbe.T.LeanLCNF.LcnfC0ContainersProof2
public import LeanQbe.T.LeanLCNF.LcnfC0ContainersProof3
import all Kraken.Separation

/-!
# Soundness Proofs for `LcnfC0Strings`, Part 3a: String<->List and `lcnf_ba_data`

Proves `Func.wp rtR2bEnv` for 3 exported runtime operations:
- `lcnf_string_to_list`
- `lcnf_string_mk`
- `lcnf_ba_data`
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF

open Std Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil

local macro "r2b_steps" : tactic => `(tactic| (try change LeanQbe.T.wp _ _ _ _ _; c0_steps))
local elab "r2b_to_group" : tactic => do
  let _ ← Lean.Elab.Tactic.tryTactic
    (Lean.Elab.Tactic.evalTactic (← `(tactic| change LeanQbe.T.wp _ _ _ _ _)))
  for _ in [:200] do
    let st0 ← Lean.Elab.Tactic.saveState
    let isGrp ← Lean.Elab.Tactic.tryTactic <| Lean.Elab.Tactic.evalTactic
      (← `(tactic| refine Lean.Elab.Tactic.exact ?_ <|>
        refine LeanQbe.T.wp_unroll_group fun _ _ => ?_))
    if isGrp then
      st0.restore
      break
    let gs0 ← Lean.Elab.Tactic.getGoals
    let ok ← Lean.Elab.Tactic.tryTactic (Lean.Elab.Tactic.evalTactic (← `(tactic| c0_step)))
    if !ok then
      st0.restore
      break
    let gs1 ← Lean.Elab.Tactic.getGoals
    if gs1.length > gs0.length then
      st0.restore
      break
local macro "r2b_call" h:term : tactic =>
  `(tactic| (refine LeanQbe.T.wp_call_of_spec _ _ ($h ?_); try c0_let_simp))

/-! ## 1. Pure UTF-8, `ExclListMem`, `IsListInHeap`, and `ByteArray`/`Array` Helpers -/

theorem utf8DecodeFrom_step {bs : List UInt8} {idx : Nat} (h : idx < bs.length) :
    utf8DecodeFrom bs idx =
      ((utf8DecodeCpAt bs idx <<< 1) ||| 1#64) ::
        utf8DecodeFrom bs (idx + utf8DecodeStepAt bs idx) := by
  conv => lhs; unfold utf8DecodeFrom
  rw [dite_eq_left h]

theorem utf8DecodeFrom_end {bs : List UInt8} {idx : Nat} (h : ¬ idx < bs.length) :
    utf8DecodeFrom bs idx = [] := by
  conv => lhs; unfold utf8DecodeFrom
  rw [dite_eq_right h]

theorem utf8LenNat_ge1 (cp : Nat) : 1 ≤ utf8LenNat cp := by
  unfold utf8LenNat; split <;> first | omega | (split <;> first | omega | (split <;> omega))

theorem utf8LenNat_le4 (cp : Nat) : utf8LenNat cp ≤ 4 := by
  unfold utf8LenNat; split <;> first | omega | (split <;> first | omega | (split <;> omega))

theorem utf8EncodeList_append (xs ys : List (BitVec 64)) :
    utf8EncodeList (xs ++ ys) = utf8EncodeList xs ++ utf8EncodeList ys := by
  induction xs with
  | nil => simp [utf8EncodeList]
  | cons x xs ih => simp [utf8EncodeList, ih, List.append_assoc]

theorem utf8EncodeList_single (hd : BitVec 64) :
    utf8EncodeList [hd] = utf8EncodeBytes ((hd >>> 1) &&& 0xffffffff#64).toNat := by
  simp [utf8EncodeList]

theorem utf8EncodeList_len_ge (xs : List (BitVec 64)) :
    xs.length ≤ (utf8EncodeList xs).length := by
  induction xs with
  | nil => simp [utf8EncodeList]
  | cons x xs ih =>
    simp only [utf8EncodeList, List.length_cons, List.length_append, utf8EncodeBytes_length]
    have := utf8LenNat_ge1 ((x >>> 1) &&& 0xffffffff#64).toNat
    omega

theorem bv64_one_and1_ne_zero : (1#64 &&& 1#64 : BitVec 64) ≠ 0#64 := by decide

theorem bv64_and1_zero_iff_even (p : BitVec 64) (hp : p.toNat % 8 = 0) :
    (p &&& 1#64) = 0#64 :=
  bv64_and1_zero_of_mod8 hp

theorem exclListMem_and1 {p : BitVec 64} {xs : List (BitVec 64)} {os : List LcnfObj}
    (h : ExclListMem p xs os) :
    ((p &&& 1#64) = 0#64 →
      ∃ hd tl nxt o restO, xs = hd :: tl ∧ os = o :: restO ∧
        o = mkListConsObj p 1#32 hd nxt ∧ p ≠ 0#64 ∧ p.toNat % 8 = 0 ∧
        ExclListMem nxt tl restO) ∧
    ((p &&& 1#64) ≠ 0#64 → p = 1#64 ∧ xs = [] ∧ os = []) := by
  cases h with
  | nil =>
    exact ⟨fun hz => absurd hz bv64_one_and1_ne_zero, fun _ => ⟨rfl, rfl, rfl⟩⟩
  | @cons _ hd nxt tl o restO ho hp0 hp8 htl =>
    have h0 := bv64_and1_zero_iff_even _ hp8
    exact ⟨fun _ => ⟨hd, tl, nxt, o, restO, rfl, rfl, ho, hp0, hp8, htl⟩,
      fun hne => absurd h0 hne⟩

theorem isListInHeap_and1 {objs : List LcnfObj} {p : BitVec 64} {xs : List (BitVec 64)}
    (h : IsListInHeap objs p xs) :
    ((p &&& 1#64) = 0#64 →
      ∃ hd tl nxt node, xs = hd :: tl ∧ node ∈ objs ∧ node.addr = p ∧
        ListConsCanon node ∧ node.fields = [hd, nxt] ∧ IsListInHeap objs nxt tl) ∧
    ((p &&& 1#64) ≠ 0#64 → p = 1#64 ∧ xs = []) := by
  cases h with
  | nil =>
    exact ⟨fun hz => absurd hz bv64_one_and1_ne_zero, fun _ => ⟨rfl, rfl⟩⟩
  | @cons _ hd nxt tl node hmem ha hc hf hp0 htl =>
    exact ⟨fun _ => ⟨hd, tl, nxt, node, rfl, hmem, ha, hc, hf, htl⟩,
      fun hne => absurd hp0 hne⟩

@[c0_load] theorem r2b_c0_load_cell64_raw8 {a v0 v1 v2 : BitVec 64} {R : Mem 64 → Prop}
    {m : Mem 64} (h : (cell64 a v0 ⋆ cell64 (a + 8#64) v1 ⋆ cell64 (a + 16#64) v2 ⋆ R) m) :
    loadVal m i64 (a + 8) = some v1 :=
  loadVal_cell64 (sep_cast h (by ac_rfl) : (cell64 (a + 8#64) v1 ⋆ (cell64 a v0 ⋆
    cell64 (a + 16#64) v2 ⋆ R)) m)

@[c0_load] theorem r2b_c0_load_cell64_raw16 {a v0 v1 v2 : BitVec 64} {R : Mem 64 → Prop}
    {m : Mem 64} (h : (cell64 a v0 ⋆ cell64 (a + 8#64) v1 ⋆ cell64 (a + 16#64) v2 ⋆ R) m) :
    loadVal m i64 (a + 16) = some v2 :=
  loadVal_cell64 (sep_cast h (by ac_rfl) : (cell64 (a + 16#64) v2 ⋆ (cell64 a v0 ⋆
    cell64 (a + 8#64) v1 ⋆ R)) m)

private theorem wp_store64_imm {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {a v0 : BitVec 64} (v : Val i64) {R : Mem 64 → Prop} {k : Expr Val Cont rs} {m : Mem 64}
    (hm : (cell64 a v0 ⋆ R) m)
    (hk : ∀ m', (cell64 a v ⋆ R) m' → wp Γ Q X k m') :
    wp Γ Q X (Expr.store (Arg.imm (t := i64) v) (Arg.var (t := i64) a) k) m :=
  wp_store_sep (by simpa only [Arg.val_var, Arg.val_imm] using store_cell64 v hm) hk

private theorem wp_store64_var {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {a v0 v : BitVec 64} {R : Mem 64 → Prop} {k : Expr Val Cont rs} {m : Mem 64}
    (hm : (cell64 a v0 ⋆ R) m)
    (hk : ∀ m', (cell64 a v ⋆ R) m' → wp Γ Q X k m') :
    wp Γ Q X (Expr.store (Arg.var (t := i64) v) (Arg.var (t := i64) a) k) m :=
  wp_store_sep (by simpa only [Arg.val_var] using store_cell64 v hm) hk

private theorem bv_box_u8_eq (b : UInt8) :
    ((BitVec.setWidth 64 (BitVec.ofNat 8 b.toNat) <<< (BitVec.signExtend 64 1#32)) ||| 1#64) =
      boxNat b.toNat := by
  have h1 : (BitVec.signExtend 64 1#32 : BitVec 64).toNat = 1 := by decide
  rw [BitVec.shiftLeft_eq', h1]
  have hb : b.toNat < 256 := b.toBitVec.isLt
  have hbit : ∀ k : Nat, (2 * k) ||| 1 = 2 * k + 1 := by
    intro k
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_or]
    cases i with
    | zero => simp
    | succ i =>
      rw [Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
      simp [show 1 / 2 = 0 by decide, show (2 * k) / 2 = k by omega,
        show (2 * k + 1) / 2 = k by omega]
  apply BitVec.eq_of_toNat_eq
  simp only [boxNat, BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ 64),
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega : b.toNat * 2 ^ 1 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : (1 : Nat) < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 2 * b.toNat + 1 < 2 ^ 64),
    show b.toNat * 2 ^ 1 = 2 * b.toNat by omega]
  exact hbit b.toNat

private theorem r2b_mkArrObj_mem_of_parts {p : BitVec 64} {rc : BitVec 32} {cap : Nat}
    {elems : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (cell64 p (mkArrObj p rc cap elems).header ⋆
        cell64 (p + 8#64) (BitVec.ofNat 64 elems.length) ⋆
        cell64 (p + 16#64) (BitVec.ofNat 64 cap) ⋆
        array64 (p + 24#64) elems ⋆
        region (p + BitVec.ofNat 64 (24 + 8 * elems.length)) (8 * (cap - elems.length)) ⋆ R) m) :
    (lcnfObjMem (mkArrObj p rc cap elems) ⋆ R) m := by
  have htag : (mkArrObj p rc cap elems).tag = arrayTag := rfl
  rw [lcnfObjMem_array_eq htag]
  exact sep_cast hm (by ac_rfl)

private theorem r2b_listCons_load8 {o : LcnfObj} (hc : ListConsCanon o) {hd nxt : BitVec 64}
    (hf : o.fields = [hd, nxt]) {R : Mem 64 → Prop} {m : Mem 64} (hm : (lcnfObjMem o ⋆ R) m) :
    loadVal m i64 (o.addr + 8#64) = some hd := by
  obtain ⟨h1, n1, hf1, hmem⟩ := lcnfObjMem_listCons_eq hc
  rw [hf] at hf1
  injection hf1 with heq1 heq2
  subst heq1
  rw [hmem] at hm
  exact r2b_c0_load_cell64_raw8
    (sep_cast hm (by ac_rfl) :
      (cell64 o.addr o.header ⋆ cell64 (o.addr + 8#64) hd ⋆
        cell64 (o.addr + 16#64) n1 ⋆ R) m)

private theorem r2b_listCons_load16 {o : LcnfObj} (hc : ListConsCanon o) {hd nxt : BitVec 64}
    (hf : o.fields = [hd, nxt]) {R : Mem 64 → Prop} {m : Mem 64} (hm : (lcnfObjMem o ⋆ R) m) :
    loadVal m i64 (o.addr + 16#64) = some nxt := by
  obtain ⟨h1, n1, hf1, hmem⟩ := lcnfObjMem_listCons_eq hc
  rw [hf] at hf1
  injection hf1 with heq1 heq2
  injection heq2 with heq3 _
  subst heq1; subst heq3
  rw [hmem] at hm
  exact r2b_c0_load_cell64_raw16
    (sep_cast hm (by ac_rfl) :
      (cell64 o.addr o.header ⋆ cell64 (o.addr + 8#64) hd ⋆
        cell64 (o.addr + 16#64) nxt ⋆ R) m)

private theorem ba_load_sz {o : LcnfObj} (hc : BaCanon o) {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (lcnfObjMem o ⋆ R) m) :
    loadVal m i64 (o.addr + 8#64) = some (BitVec.ofNat 64 o.scalarData.length) := by
  have hs := lcnfObjMem_sarray_elim hc hm
  have hars : o.arrSize = o.scalarData.length := hc.2.2.2.2.2.2.1
  rw [hars] at hs
  exact loadVal_cell64 (sep_cast hs (by ac_rfl) :
    (cell64 (o.addr + 8#64) (BitVec.ofNat 64 o.scalarData.length) ⋆
      (cell64 o.addr o.header ⋆ cell64 (o.addr + 16#64) (BitVec.ofNat 64 o.cap) ⋆
        bytes (o.addr + 24#64) o.scalarData ⋆
        region (o.addr + BitVec.ofNat 64 (24 + o.scalarData.length))
          (baAllocBytes o.cap - (24 + o.scalarData.length)) ⋆ R)) m)

private theorem lcnfHeap_focus_obj {objs : List LcnfObj} {o : LcnfObj} {k : Nat}
    (hk : k < objs.length) (hobj : objs[k] = o) :
    lcnfHeap objs =
      (lcnfObjMem o ⋆ (lcnfHeap (objs.take k) ⋆ lcnfHeap (objs.drop (k + 1)))) := by
  rw [lcnfHeap_focus objs hk, hobj]

private theorem bv_sext1_toNat : (BitVec.signExtend 64 1#32 : BitVec 64).toNat = 1 := by decide

private theorem r2b_listConsHeaderWord_eq :
    (72620647070564353 : BitVec 64) = listConsHeaderWord := by
  decide

/-! ## 2. `lcnf_string_to_list` WP Proof -/

theorem lcnf_string_to_list_wp :
    ∀ xs m Q X, lcnfStringToListSpec xs m Q X →
      Func.wp rtR2bEnv lcnf_string_to_list_body xs m Q X := by
  intro ⟨rt, s, ⟨⟩⟩ m Q X hPre
  dsimp only [Func.wp, lcnf_string_to_list_body, lcnfStringToListSpec] at hPre ⊢
  rcases hPre with ⟨st, sObj, objs, R, hsMem, hsAddr, hcan, hwfObjs, hrc1Ok, hremHav, hm, hk⟩
  let bs := strPayload sObj
  let cps := utf8DecodeFrom bs 0
  have hplenLt := str_payload_lt_max sObj hcan
  have hsz64 : bs.length < 2 ^ 64 := by
    dsimp only [bs]; unfold strMaxCap at hplenLt; omega
  have hszTo : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsz64]
  obtain ⟨kS, hkS, hobjS⟩ := List.getElem_of_mem hsMem
  have hfocusS := lcnfHeap_focus_obj hkS hobjS
  have hloadSz : loadVal m i64 (s + 8#64) = some (BitVec.ofNat 64 (bs.length + 1)) := by
    have hmS : (lcnfObjMem sObj ⋆ (lcnfHeap (objs.take kS) ⋆ lcnfHeap (objs.drop (kS + 1)) ⋆
        rtC0Inv rt st ⋆ R)) m := by
      rw [hfocusS] at hm; exact sep_cast hm (by ac_rfl)
    rw [← hsAddr]
    exact str_load_sz hcan hmS
  r2b_steps
  apply wp_load_of hloadSz
  r2b_steps
  rw [str_sz_sub1_eq sObj hcan]
  refine wp_loop_group
    (fun n (xs : Tup Val [i64, i64]) mL =>
      ∃ (posNat : Nat) (acc : List (BitVec 64)) (revObjs : List LcnfObj) (st1 : RtC0State),
        xs.2.1 = BitVec.ofNat 64 posNat ∧
        posNat ≤ bs.length ∧
        (utf8DecodeFrom bs posNat).length = n ∧
        st1.PreservesMeta st ∧
        st1.rem ≤ st.rem ∧
        24 * n ≤ st1.rem ∧
        ExclListMem xs.1 acc revObjs ∧
        acc.reverse ++ utf8DecodeFrom bs posNat = cps ∧
        (lcnfHeap revObjs ⋆ rtC0Inv rt st1 ⋆ lcnfHeap objs ⋆ R) mL) ?_ ?_
  · intro J1 n ⟨rev, pos, ⟨⟩⟩ mL hL1
      ⟨posNat, acc, revObjs, st1, hposEq, hposLe, hnEq, hpr1, hrem1, hremHav1, hrev, hsplit, hmL⟩
    subst hposEq
    have hpos64 : posNat < 2 ^ 64 := by omega
    have hposTo : (BitVec.ofNat 64 posNat).toNat = posNat := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpos64]
    by_cases hlt : posNat < bs.length
    · have hcmpT : BitVec.ofNat 64 posNat < BitVec.ofNat 64 bs.length := by
        rw [BitVec.lt_def, hposTo, hszTo]; exact hlt
      have hdecStepPos := utf8DecodeStepAt_pos hlt
      let step := utf8DecodeStepAt bs posNat
      let cp := utf8DecodeCpAt bs posNat
      have hstep64 : step < 2 ^ 64 := by dsimp only [step]; omega
      have hstepTo : (BitVec.ofNat 64 step).toNat = step := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hstep64]
      have huf := utf8DecodeFrom_step hlt
      have hnPos : n = (utf8DecodeFrom bs (posNat + step)).length + 1 := by
        rw [← hnEq, huf, List.length_cons]
      have hrem24 : 24 ≤ st1.rem := by omega
      r2b_steps
      all_goals first
        | (exfalso
           exact (by assumption : ¬ BitVec.ofNat 64 posNat < BitVec.ofNat 64 bs.length) hcmpT)
        | (r2b_call rtR2bEnv_r2b_utf8_decode_cp
           dsimp only [r2bUtf8DecodeCpSpec, vals, Tup.map, Arg.val]
           refine ⟨bs, strRest sObj ⋆ lcnfHeap (objs.take kS) ⋆ lcnfHeap (objs.drop (kS + 1)) ⋆
             lcnfHeap revObjs ⋆ rtC0Inv rt st1 ⋆ R, hszTo.symm, ?_, ?_⟩
           · have hm0 : (lcnfObjMem sObj ⋆ (lcnfHeap (objs.take kS) ⋆
                 lcnfHeap (objs.drop (kS + 1)) ⋆ lcnfHeap revObjs ⋆ rtC0Inv rt st1 ⋆ R)) mL := by
               rw [hfocusS] at hmL; exact sep_cast hmL (by ac_rfl)
             rw [strObj_eq_bytes_rest hcan, hsAddr] at hm0
             exact sep_cast hm0 (by ac_rfl)
           · try dsimp only
             rw [hposTo]
             r2b_steps
             r2b_call rtR2bEnv_r2b_utf8_decode_step
             dsimp only [r2bUtf8DecodeStepSpec, vals, Tup.map, Arg.val]
             refine ⟨bs, strRest sObj ⋆ lcnfHeap (objs.take kS) ⋆ lcnfHeap (objs.drop (kS + 1)) ⋆
               lcnfHeap revObjs ⋆ rtC0Inv rt st1 ⋆ R, hszTo.symm, ?_, ?_⟩
             · have hm0 : (lcnfObjMem sObj ⋆ (lcnfHeap (objs.take kS) ⋆
                   lcnfHeap (objs.drop (kS + 1)) ⋆ lcnfHeap revObjs ⋆ rtC0Inv rt st1 ⋆ R)) mL := by
                 rw [hfocusS] at hmL; exact sep_cast hmL (by ac_rfl)
               rw [strObj_eq_bytes_rest hcan, hsAddr] at hm0
               exact sep_cast hm0 (by ac_rfl)
             · try dsimp only
               rw [hposTo]
               r2b_steps
               r2b_call rtR2bEnv_lcnf_alloc
               dsimp only [lcnfAllocRemSpec, vals, Tup.map, Arg.val]
               have ha24 : align8 (24 : BitVec 64).toNat = 24 := by decide
               rw [ha24]
               refine ⟨st1, lcnfHeap revObjs ⋆ lcnfHeap objs ⋆ R,
                 by decide, by unfold rtMinObjBytes; decide, by unfold rtMaxObjBytes; decide,
                 Or.inr hrem24, sep_cast hmL (by ac_rfl),
                 fun node st2 m2 hnd0 hnd8 hpr2 hrem2Lo hrem2Hi hm2 => ?_⟩
               try dsimp only
               obtain ⟨w0, w1, w2, hm2c⟩ := region_to_3cells_rem (by decide : 24 ≤ 24)
                 (by decide : 24 ≤ 2 ^ 64)
                 (sep_cast hm2 (by ac_rfl) :
                   (region node 24 ⋆ (rtC0Inv rt st2 ⋆ lcnfHeap revObjs ⋆ lcnfHeap objs ⋆ R)) m2)
               rw [show 24 - 24 = 0 by rfl, region_zero] at hm2c
               have hm2c0 : (cell64 node w0 ⋆ (cell64 (node + 8#64) w1 ⋆
                   cell64 (node + 16#64) w2 ⋆ rtC0Inv rt st2 ⋆ lcnfHeap revObjs ⋆
                   lcnfHeap objs ⋆ R)) m2 := sep_cast hm2c (by ac_rfl)
               apply wp_store64_imm (72620647070564353 : BitVec 64) hm2c0
               intro m3 hm3
               r2b_steps
               have hm3' : (cell64 (node + 8#64) w1 ⋆ (cell64 node listConsHeaderWord ⋆
                   cell64 (node + 16#64) w2 ⋆ rtC0Inv rt st2 ⋆ lcnfHeap revObjs ⋆
                   lcnfHeap objs ⋆ R)) m3 := by
                 rw [r2b_listConsHeaderWord_eq] at hm3
                 exact sep_cast hm3 (by ac_rfl)
               let hdVal := (cp <<< (BitVec.signExtend 64 1#32)) ||| 1#64
               have hsh : hdVal = (cp <<< 1) ||| 1#64 := by
                 dsimp only [hdVal]; rw [BitVec.shiftLeft_eq', bv_sext1_toNat]
               apply wp_store64_var hm3'
               intro m4 hm4
               r2b_steps
               have hm4' : (cell64 (node + 16#64) w2 ⋆ (cell64 node listConsHeaderWord ⋆
                   cell64 (node + 8#64) ((cp <<< 1) ||| 1#64) ⋆ rtC0Inv rt st2 ⋆
                   lcnfHeap revObjs ⋆ lcnfHeap objs ⋆ R)) m4 := by
                 change (cell64 (node + 8#64) hdVal ⋆ _) m4 at hm4
                 rw [hsh] at hm4
                 exact sep_cast hm4 (by ac_rfl)
               apply wp_store64_var hm4'
               intro m5 hm5
               r2b_steps
               let oNew := mkListConsObj node 1#32 ((cp <<< 1) ||| 1#64) rev
               have hm5Mem : (lcnfObjMem oNew ⋆ (lcnfHeap revObjs ⋆ rtC0Inv rt st2 ⋆
                   lcnfHeap objs ⋆ R)) m5 := by
                 try rw [BitVec.or_comm 1#64] at hm5
                 exact mkListConsObj_mem hnd0 hnd8
                   (sep_cast hm5 (by ac_rfl) :
                     (cell64 node listConsHeaderWord ⋆
                       cell64 (node + 8#64) ((cp <<< 1) ||| 1#64) ⋆
                       cell64 (node + 16#64) rev ⋆
                       (lcnfHeap revObjs ⋆ rtC0Inv rt st2 ⋆ lcnfHeap objs ⋆ R)) m5)
               have hm5Heap : (lcnfHeap (oNew :: revObjs) ⋆ rtC0Inv rt st2 ⋆
                   lcnfHeap objs ⋆ R) m5 := by
                 simp only [lcnfHeap]; exact sep_cast hm5Mem (by ac_rfl)
               have haddPos : BitVec.ofNat 64 posNat + BitVec.ofNat 64 step =
                   BitVec.ofNat 64 (posNat + step) :=
                 (BitVec.ofNat_add posNat step).symm
               rw [haddPos]
               refine hL1 (utf8DecodeFrom bs (posNat + step)).length (node,
                 BitVec.ofNat 64 (posNat + step), ()) m5 (by omega)
                 ⟨posNat + step, ((cp <<< 1) ||| 1#64) :: acc, oNew :: revObjs, st2, rfl,
                   hdecStepPos.2, rfl, hpr1.trans hpr2, by omega, by omega,
                   ExclListMem.cons rfl hnd0 hnd8 hrev, ?_, hm5Heap⟩
               simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
               rw [← huf, hsplit])
    · have hge : bs.length ≤ posNat := Nat.not_lt.mp hlt
      have hposEqLen : posNat = bs.length := by omega
      have hcmpF : ¬ BitVec.ofNat 64 posNat < BitVec.ofNat 64 bs.length := by
        rw [BitVec.lt_def, hposTo, hszTo]; exact hlt
      have hufEnd : utf8DecodeFrom bs posNat = [] := utf8DecodeFrom_end hlt
      rw [hufEnd, List.append_nil] at hsplit
      r2b_steps
      all_goals first
        | (exfalso; exact hcmpF (by assumption))
        | (r2b_call rtR2bEnv_r2_dec_obj
           dsimp only [r2DecObjSpec, vals, Tup.map, Arg.val]
           have hnotNull : ¬ (s = 0#64 ∨ (s &&& 1#64) ≠ 0#64) := by
             simp [hsAddr ▸ hcan.1, hsAddr ▸ bv64_and1_zero_of_mod8 hcan.2.1]
           rw [ite_eq_right hnotNull]
           refine ⟨st1, objs, lcnfHeap revObjs ⋆ R, ⟨sObj, hsMem, hsAddr, fun hrc1 => ?_⟩,
             hwfObjs, sep_cast hmL (by ac_rfl), fun st2 objs' m2 hpr2 hrem2 hdec hm2 => ?_⟩
           · rw [RtC0State.workCap_eq_of_preservesMeta hpr1]; exact hrc1Ok hrc1
           · try dsimp only
             refine wp_loop_group
               (fun n2 (xs : Tup Val [i64, i64]) mR =>
                 ∃ revRem resAcc revOs resOs,
                   revRem.length = n2 ∧
                   ExclListMem xs.1 revRem revOs ∧
                   ExclListMem xs.2.1 resAcc resOs ∧
                   revRem.reverse ++ resAcc = cps ∧
                   (lcnfHeap revOs ⋆ lcnfHeap resOs ⋆ rtC0Inv rt st2 ⋆
                     lcnfHeap objs' ⋆ R) mR) ?_ ?_
             · intro J2 n2 ⟨rv, rs, ⟨⟩⟩ mR hL2
                 ⟨revRem, resAcc, revOs, resOs, hn2, hrv, hrs, hcpsEq, hmR⟩
               have hand := exclListMem_and1 hrv
               by_cases hz : (rv &&& 1#64) = 0#64
               · obtain ⟨hd, tl, nxt, o, restO, hrevEq, hosEq, hoEq, hp0, hp8, htl⟩ := hand.1 hz
                 subst hrevEq; subst hosEq; subst hoEq
                 have hcl : ListConsCanon (mkListConsObj rv 1#32 hd nxt) :=
                   mkListConsObj_canon hp0 hp8 (by decide)
                 obtain ⟨hdx, nxtx, hft, hmemO⟩ := lcnfObjMem_listCons_eq hcl
                 dsimp only [mkListConsObj] at hft
                 injection hft with h1 h2; injection h2 with h3 _
                 subst h1; subst h3
                 have hmR' : (cell64 rv (mkListConsObj rv 1#32 hd nxt).header ⋆
                     cell64 (rv + 8#64) hd ⋆ cell64 (rv + 16#64) nxt ⋆
                     (lcnfHeap restO ⋆ lcnfHeap resOs ⋆ rtC0Inv rt st2 ⋆
                       lcnfHeap objs' ⋆ R)) mR := by
                   simp only [lcnfHeap] at hmR
                   rw [hmemO] at hmR
                   exact sep_cast hmR (by ac_rfl)
                 r2b_steps
                 all_goals first
                   | (exfalso; exact (by assumption : ¬ (rv &&& 1#64) = 0#64) hz)
                   | (apply wp_load_of (r2b_c0_load_cell64_raw16 hmR')
                      r2b_steps
                      have hmReady : (cell64 (rv + 16#64) nxt ⋆ (cell64 rv listConsHeaderWord ⋆
                        cell64 (rv + 8#64) hd ⋆ lcnfHeap restO ⋆ lcnfHeap resOs ⋆
                        rtC0Inv rt st2 ⋆ lcnfHeap objs' ⋆ R)) mR := by
                        rw [mkListConsObj_header] at hmR'
                        exact sep_cast hmR' (by ac_rfl)
                      apply wp_store64_var hmReady
                      intro mW hmW
                      r2b_steps
                      apply hL2 tl.length (nxt, rv, ()) mW (by rw [← hn2]; simp)
                      let oNew := mkListConsObj rv 1#32 hd rs
                      have hmemNew : (lcnfObjMem oNew ⋆ (lcnfHeap restO ⋆ lcnfHeap resOs ⋆
                          rtC0Inv rt st2 ⋆ lcnfHeap objs' ⋆ R)) mW :=
                        mkListConsObj_mem hp0 hp8
                          (sep_cast hmW (by ac_rfl) :
                            (cell64 rv listConsHeaderWord ⋆ cell64 (rv + 8#64) hd ⋆
                              cell64 (rv + 16#64) rs ⋆ (lcnfHeap restO ⋆ lcnfHeap resOs ⋆
                                rtC0Inv rt st2 ⋆ lcnfHeap objs' ⋆ R)) mW)
                      refine ⟨tl, hd :: resAcc, restO, oNew :: resOs, rfl, htl,
                        ExclListMem.cons rfl hp0 hp8 hrs, ?_, ?_⟩
                      · simp only [List.reverse_cons, List.append_assoc,
                          List.singleton_append] at hcpsEq ⊢
                        exact hcpsEq
                      · simp only [lcnfHeap]; exact sep_cast hmemNew (by ac_rfl))
               · obtain ⟨_, hrNil, hoNil⟩ := hand.2 hz
                 subst hrNil; subst hoNil
                 simp only [List.reverse_nil, List.nil_append] at hcpsEq
                 subst hcpsEq
                 simp only [lcnfHeap, emp_sep] at hmR
                 r2b_steps
                 all_goals first
                   | (exfalso; exact hz (by assumption))
                   | (exact hk rs st2 resOs objs' mR (hpr1.trans hpr2) (by omega) hrs hdec
                        (sep_cast hmR (by ac_rfl)))
             · intro J2 hJ2
               exact @hJ2 acc.length (rev, 1#64, ()) m2
                 ⟨acc, [], revObjs, [], rfl, hrev, ExclListMem.nil,
                   by simpa using hsplit, (by
                     simp only [lcnfHeap, sep_emp]
                     exact sep_cast hm2 (by ac_rfl))⟩)
  · intro J1 hJ1
    exact @hJ1 (utf8DecodeFrom bs 0).length (1#64, 0#64, ()) m
      ⟨0, [], [], st, rfl, Nat.zero_le _, rfl,
        RtC0State.PreservesMeta.refl st, Nat.le_refl _, hremHav, ExclListMem.nil, rfl,
        (by simp only [lcnfHeap, emp_sep]; exact sep_cast hm (by ac_rfl))⟩

/-! ## 3. `lcnf_string_mk` WP Proof -/

theorem lcnf_string_mk_wp :
    ∀ xs m Q X, lcnfStringMkSpec xs m Q X → Func.wp rtR2bEnv lcnf_string_mk_body xs m Q X := by
  intro ⟨rt, cs, ⟨⟩⟩ m Q X hPre
  dsimp only [Func.wp, lcnf_string_mk_body, lcnfStringMkSpec] at hPre ⊢
  rcases hPre with ⟨st, cps, objs, R, hlist, hwfObjs, hcsPre, hm, hPost⟩
  let bs := utf8EncodeList cps
  refine wp_loop_group
    (fun n (xs : Tup Val [i64, i64, i64]) mL =>
      mL = m ∧
      ∃ pfx rem,
        pfx ++ rem = cps ∧
        rem.length = n ∧
        IsListInHeap objs xs.2.2.1 rem ∧
        (utf8EncodeList pfx).length < strMaxCap ∧
        xs.1 = BitVec.ofNat 64 (utf8EncodeList pfx).length ∧
        xs.2.1 = BitVec.ofNat 64 pfx.length) ?_ ?_
  · intro J1 n ⟨tb, cl, cur, ⟨⟩⟩ mL hL1 ⟨hmEq, pfx, rem, hsp, hnEq, hrem, htbLt, htbEq, hclEq⟩
    subst hmEq; subst htbEq; subst hclEq
    have htb64 : (utf8EncodeList pfx).length < 2 ^ 64 := by unfold strMaxCap at htbLt; omega
    have htbTo : (BitVec.ofNat 64 (utf8EncodeList pfx).length).toNat =
        (utf8EncodeList pfx).length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htb64]
    have hpfxLt : pfx.length < strMaxCap :=
      Nat.lt_of_le_of_lt (utf8EncodeList_len_ge pfx) htbLt
    have hpfx64 : pfx.length < 2 ^ 64 := by unfold strMaxCap at hpfxLt; omega
    have hand := isListInHeap_and1 hrem
    by_cases hcur : (cur &&& 1#64) = 0#64
    · obtain ⟨hd, tl, nxt, node, hremEq, hmemN, haN, hcN, hfN, htl⟩ := hand.1 hcur
      subst hremEq
      obtain ⟨kN, hkN, hobjN⟩ := List.getElem_of_mem hmemN
      have hmN : (lcnfObjMem node ⋆ (lcnfHeap (objs.take kN) ⋆ lcnfHeap (objs.drop (kN + 1)) ⋆
          rtC0Inv rt st ⋆ R)) mL := by
        rw [lcnfHeap_focus_obj hkN hobjN] at hm
        exact sep_cast hm (by ac_rfl)
      have hloadHd : loadVal mL i64 (cur + 8#64) = some hd := by
        dsimp only at haN; rw [← haN]; exact r2b_listCons_load8 hcN hfN hmN
      have hloadNxt : loadVal mL i64 (cur + 16#64) = some nxt := by
        dsimp only at haN; rw [← haN]; exact r2b_listCons_load16 hcN hfN hmN
      let cpNat := ((hd >>> 1) &&& (4294967295 : BitVec 64)).toNat
      let stepLen := utf8LenNat cpNat
      have hstepLe4 : stepLen ≤ 4 := utf8LenNat_le4 cpNat
      have hstep64 : stepLen < 2 ^ 64 := by
        dsimp only [stepLen]; exact Nat.lt_of_le_of_lt hstepLe4 (by decide)
      have hstepTo : (BitVec.ofNat 64 stepLen).toNat = stepLen := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hstep64]
      have hcpShift : (hd >>> BitVec.signExtend 64 1#32) = hd >>> 1 := by
        rw [BitVec.ushiftRight_eq', bv_sext1_toNat]
      have hsumEq : BitVec.ofNat 64 (utf8EncodeList pfx).length +
          BitVec.ofNat 64 (utf8LenNat ((hd >>> 1) &&& (4294967295 : BitVec 64)).toNat) =
          BitVec.ofNat 64 ((utf8EncodeList (pfx ++ [hd])).length) := by
        rw [utf8EncodeList_append, utf8EncodeList_single, List.length_append,
          utf8EncodeBytes_length, show (0xffffffff#64 : BitVec 64) = 4294967295 from rfl]
        exact (BitVec.ofNat_add _ _).symm
      have hsum64 : (utf8EncodeList (pfx ++ [hd])).length < 2 ^ 64 := by
        rw [utf8EncodeList_append, utf8EncodeList_single, List.length_append,
          utf8EncodeBytes_length]
        have h4 : utf8LenNat ((hd >>> 1) &&& 0xffffffff#64).toNat ≤ 4 := hstepLe4
        unfold strMaxCap at htbLt; omega
      have hsumTo : (BitVec.ofNat 64 (utf8EncodeList (pfx ++ [hd])).length).toNat =
          (utf8EncodeList (pfx ++ [hd])).length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsum64]
      r2b_steps
      all_goals first
        | (exfalso; exact (by assumption : ¬ (cur &&& 1#64) = 0#64) hcur)
        | (apply wp_load_of hloadHd
           r2b_steps
           try rw [hcpShift]
           r2b_call rtR2bEnv_r2b_utf8_len
           dsimp only [r2bUtf8LenSpec, vals, Tup.map, Arg.val]
           try dsimp only
           try rw [show (4294967295#64 : BitVec 64) = 4294967295 from rfl]
           rw [hsumEq]
           by_cases hov : 268435415 ≤ (utf8EncodeList (pfx ++ [hd])).length
           · have hcmpT : (268435415#64 : BitVec 64) ≤
                 BitVec.ofNat 64 (utf8EncodeList (pfx ++ [hd])).length := by
               rw [BitVec.le_def, hsumTo]; exact hov
             have hbsGe : strMaxCap ≤ bs.length := by
               have hsp' : cps = (pfx ++ [hd]) ++ tl := by rw [← hsp]; simp
               dsimp only [bs]; rw [hsp', utf8EncodeList_append, List.length_append]
               unfold strMaxCap; omega
             rw [ite_eq_left hbsGe] at hPost
             r2b_steps
             all_goals first
               | (exfalso; exact (by assumption : BitVec.ofNat 64 _ < 268435415#64).not_ge hcmpT)
               | exact hPost
           · have hok : (utf8EncodeList (pfx ++ [hd])).length < strMaxCap := by
               unfold strMaxCap; omega
             have hcmpF : ¬ (268435415#64 : BitVec 64) ≤
                 BitVec.ofNat 64 (utf8EncodeList (pfx ++ [hd])).length := by
               rw [BitVec.le_def, hsumTo,
                 show (268435415#64 : BitVec 64).toNat = 268435415 from rfl]
               omega
             r2b_steps
             all_goals first
               | (exfalso; exact hcmpF (by assumption))
               | (apply wp_load_of hloadNxt
                  r2b_steps
                  have haddCl : BitVec.ofNat 64 pfx.length + (1 : BitVec 64) =
                      BitVec.ofNat 64 (pfx ++ [hd]).length := by
                    simp only [List.length_append, List.length_singleton]
                    exact (BitVec.ofNat_add _ 1).symm
                  try rw [show (4294967295#64 : BitVec 64) = 4294967295 from rfl]
                  rw [hsumEq, haddCl]
                  refine hL1 tl.length (BitVec.ofNat 64 (utf8EncodeList (pfx ++ [hd])).length,
                    BitVec.ofNat 64 (pfx ++ [hd]).length, nxt, ()) mL
                    (by rw [← hnEq]; simp)
                    ⟨rfl, pfx ++ [hd], tl, by rw [← hsp]; simp, rfl, htl, hok, rfl, rfl⟩))
    · obtain ⟨hcsEq, hnil⟩ := hand.2 hcur
      subst hnil
      rw [List.append_nil] at hsp
      have hpfxEq : pfx = cps := hsp
      have hltMax : bs.length < strMaxCap := by
        dsimp only [bs]; rw [← hpfxEq]; exact htbLt
      rw [ite_eq_right (Nat.not_le.mpr hltMax)] at hPost
      rcases hPost with ⟨hav, hk⟩
      have hcap64 : bs.length + 1 < 2 ^ 64 := by unfold strMaxCap at hltMax; omega
      have hcapEq : BitVec.ofNat 64 bs.length + (1 : BitVec 64) =
          BitVec.ofNat 64 (bs.length + 1) :=
        (BitVec.ofNat_add bs.length 1).symm
      have hcapTo : (BitVec.ofNat 64 (bs.length + 1)).toNat = bs.length + 1 := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcap64]
      r2b_steps
      all_goals first
        | (exfalso; exact hcur (by assumption))
        | (change LeanQbe.T.wp _ _ _ _ _
           rw [hpfxEq] at *
           dsimp only [bs] at hcapEq hcapTo ⊢
           try rw [hcapEq]
           try rw [show BitVec.ofNat 64 (utf8EncodeList cps).length + 1#64 =
             BitVec.ofNat 64 ((utf8EncodeList cps).length + 1) from
             (BitVec.ofNat_add _ 1).symm]
           r2b_call rtR2bEnv_r2b_str_alloc_cap
           dsimp only [r2bStrAllocCapSpec, vals, Tup.map, Arg.val]
           have hbsTo : (BitVec.ofNat 64 (utf8EncodeList cps).length).toNat =
               (utf8EncodeList cps).length := by
             rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold strMaxCap at hltMax; omega)]
           rw [hbsTo, hcapTo, ite_eq_left ⟨hltMax, Nat.lt_succ_self _, hltMax⟩]
           refine ⟨st, lcnfHeap objs ⋆ R, hav, sep_cast hm (by ac_rfl),
             fun dst st1 m1 hdst0 hdst8 hpr1 hrem1 _ hm1 => ?_⟩
           try dsimp only
           let rest2 := rtC0Inv rt st1 ⋆ cell64 dst strHeaderWord ⋆
             cell64 (dst + 8#64) (BitVec.ofNat 64 bs.length + 1#64) ⋆
             cell64 (dst + 16#64) (BitVec.ofNat 64 (bs.length + 1)) ⋆
             cell64 (dst + 24#64) (BitVec.ofNat 64 cps.length) ⋆
             bytes (dst + 32#64 + BitVec.ofNat 64 bs.length) [(0 : UInt8)] ⋆
             region (dst + 32#64 + BitVec.ofNat 64 bs.length + 1#64)
               (strAllocBytes (bs.length + 1) - (32 + bs.length + 1)) ⋆
             lcnfHeap objs ⋆ R
           refine wp_loop_group
             (fun n2 (xs : Tup Val [i64, i64]) mL2 =>
               ∃ pfx2 rem2,
                 pfx2 ++ rem2 = cps ∧
                 rem2.length = n2 ∧
                 IsListInHeap objs xs.1 rem2 ∧
                 xs.2.1 = BitVec.ofNat 64 (utf8EncodeList pfx2).length ∧
                 (bytes (dst + 32#64) (utf8EncodeList pfx2) ⋆
                   region (dst + 32#64 + BitVec.ofNat 64 (utf8EncodeList pfx2).length)
                     (utf8EncodeList rem2).length ⋆ rest2) mL2) ?_ ?_
           · intro J2 n2 ⟨cur2, pos2, ⟨⟩⟩ mL2 hL2
               ⟨pfx2, rem2, hsp2, hn2, hrem2, hpos2Eq, hmL2⟩
             subst hpos2Eq
             have hand2 := isListInHeap_and1 hrem2
             by_cases hcur2 : (cur2 &&& 1#64) = 0#64
             · obtain ⟨hd, tl, nxt, node, hrem2Eq, hmemN, haN, hcN, hfN, htl⟩ := hand2.1 hcur2
               subst hrem2Eq
               obtain ⟨kN, hkN, hobjN⟩ := List.getElem_of_mem hmemN
               have hfocusN := lcnfHeap_focus_obj hkN hobjN
               have hmL2N : (lcnfObjMem node ⋆ (lcnfHeap (objs.take kN) ⋆
                   lcnfHeap (objs.drop (kN + 1)) ⋆ bytes (dst + 32#64) (utf8EncodeList pfx2) ⋆
                   region (dst + 32#64 + BitVec.ofNat 64 (utf8EncodeList pfx2).length)
                     (utf8EncodeList (hd :: tl)).length ⋆
                   rtC0Inv rt st1 ⋆ cell64 dst strHeaderWord ⋆
                   cell64 (dst + 8#64) (BitVec.ofNat 64 bs.length + 1#64) ⋆
                   cell64 (dst + 16#64) (BitVec.ofNat 64 (bs.length + 1)) ⋆
                   cell64 (dst + 24#64) (BitVec.ofNat 64 cps.length) ⋆
                   bytes (dst + 32#64 + BitVec.ofNat 64 bs.length) [(0 : UInt8)] ⋆
                   region (dst + 32#64 + BitVec.ofNat 64 bs.length + 1#64)
                     (strAllocBytes (bs.length + 1) - (32 + bs.length + 1)) ⋆ R)) mL2 := by
                 dsimp only [rest2] at hmL2; rw [hfocusN] at hmL2; exact sep_cast hmL2 (by ac_rfl)
               have hloadHd : loadVal mL2 i64 (cur2 + 8#64) = some hd := by
                 dsimp only at haN; rw [← haN]; exact r2b_listCons_load8 hcN hfN hmL2N
               let cp2 := (hd >>> 1) &&& (4294967295 : BitVec 64)
               let seg := utf8EncodeBytes cp2.toNat
               have hremLen : (utf8EncodeList (hd :: tl)).length =
                   seg.length + (utf8EncodeList tl).length := by
                 dsimp only [seg, cp2]
                 simp only [utf8EncodeList, List.length_append, utf8EncodeBytes_length]
                 rw [show (0xffffffff#64 : BitVec 64) = 4294967295 from rfl]
               have hbsEq : bs.length = (utf8EncodeList pfx2).length +
                   (seg.length + (utf8EncodeList tl).length) := by
                 have h0 : bs = utf8EncodeList pfx2 ++ utf8EncodeList (hd :: tl) := by
                   dsimp only [bs]; rw [← hsp2, utf8EncodeList_append]
                 rw [h0, List.length_append, hremLen]
               have hremFit : (utf8EncodeList (hd :: tl)).length ≤ 2 ^ 64 := by
                 unfold strMaxCap at hltMax; omega
               r2b_steps
               all_goals first
                 | (exfalso; exact (by assumption : ¬ (cur2 &&& 1#64) = 0#64) hcur2)
                 | (apply wp_load_of hloadHd
                    r2b_steps
                    try rw [show (hd >>> BitVec.signExtend 64 1#32) = hd >>> 1 by
                      rw [BitVec.ushiftRight_eq', bv_sext1_toNat]]
                    r2b_call rtR2bEnv_r2b_utf8_write
                    dsimp only [r2bUtf8WriteSpec, vals, Tup.map, Arg.val]
                    refine ⟨(utf8EncodeList (hd :: tl)).length,
                      bytes (dst + 32#64) (utf8EncodeList pfx2) ⋆ rest2,
                      (by show seg.length ≤ (utf8EncodeList (hd :: tl)).length
                          rw [hremLen]; exact Nat.le_add_right _ _),
                      hremFit,
                      (sep_cast hmL2 (by ac_rfl) :
                        (region (dst + 32#64 + BitVec.ofNat 64 (utf8EncodeList pfx2).length)
                          (utf8EncodeList (hd :: tl)).length ⋆
                          (bytes (dst + 32#64) (utf8EncodeList pfx2) ⋆ rest2)) mL2),
                      fun mW hmW => ?_⟩
                    try dsimp only
                    r2b_steps
                    have hmWN : (lcnfObjMem node ⋆ (lcnfHeap (objs.take kN) ⋆
                        lcnfHeap (objs.drop (kN + 1)) ⋆ bytes (dst + 32#64) (utf8EncodeList pfx2) ⋆
                        bytes (dst + 32#64 + BitVec.ofNat 64 (utf8EncodeList pfx2).length)
                          (utf8EncodeBytes ((hd >>> 1) &&& (4294967295 : BitVec 64)).toNat) ⋆
                        region (dst + 32#64 + BitVec.ofNat 64 (utf8EncodeList pfx2).length +
                            BitVec.ofNat 64
                              (utf8EncodeBytes ((hd >>> 1) &&&
                                (4294967295 : BitVec 64)).toNat).length)
                          ((utf8EncodeList (hd :: tl)).length -
                            (utf8EncodeBytes ((hd >>> 1) &&&
                              (4294967295 : BitVec 64)).toNat).length) ⋆
                        rtC0Inv rt st1 ⋆ cell64 dst strHeaderWord ⋆
                        cell64 (dst + 8#64) (BitVec.ofNat 64 bs.length + 1#64) ⋆
                        cell64 (dst + 16#64) (BitVec.ofNat 64 (bs.length + 1)) ⋆
                        cell64 (dst + 24#64) (BitVec.ofNat 64 cps.length) ⋆
                        bytes (dst + 32#64 + BitVec.ofNat 64 bs.length) [(0 : UInt8)] ⋆
                        region (dst + 32#64 + BitVec.ofNat 64 bs.length + 1#64)
                          (strAllocBytes (bs.length + 1) - (32 + bs.length + 1)) ⋆ R)) mW := by
                      dsimp only [rest2] at hmW
                      rw [hfocusN, show (32 : BitVec 64) = 32#64 from rfl] at hmW
                      exact sep_cast hmW (by ac_rfl)
                    have hloadNxt' : loadVal mW i64 (cur2 + 16#64) = some nxt := by
                      dsimp only at haN; rw [← haN]; exact r2b_listCons_load16 hcN hfN hmWN
                    apply wp_load_of hloadNxt'
                    r2b_steps
                    have hsegEq : utf8EncodeBytes ((hd >>> 1) &&& (4294967295 : BitVec 64)).toNat =
                        seg := rfl
                    have hApp := bytes_append (dst + 32#64) (utf8EncodeList pfx2) seg
                      (by unfold strMaxCap at hltMax; omega)
                    have hnewPfx : utf8EncodeList (pfx2 ++ [hd]) =
                        utf8EncodeList pfx2 ++ seg := by
                      rw [utf8EncodeList_append, utf8EncodeList_single]
                      rw [show (0xffffffff#64 : BitVec 64) = 4294967295 from rfl]
                    have hApp' : bytes (dst + 32#64) (utf8EncodeList (pfx2 ++ [hd])) =
                        (bytes (dst + 32#64) (utf8EncodeList pfx2) ⋆
                          bytes (dst + 32#64 + BitVec.ofNat 64 (utf8EncodeList pfx2).length)
                            seg) := by
                      rw [hnewPfx, hApp]
                    have hposAdd : BitVec.ofNat 64 (utf8EncodeList pfx2).length +
                        BitVec.ofNat 64 seg.length =
                        BitVec.ofNat 64 (utf8EncodeList (pfx2 ++ [hd])).length := by
                      rw [hnewPfx, List.length_append]
                      exact (BitVec.ofNat_add _ _).symm
                    have hptrAdd : dst + 32#64 + BitVec.ofNat 64 (utf8EncodeList pfx2).length +
                        BitVec.ofNat 64 seg.length =
                        dst + 32#64 + BitVec.ofNat 64 (utf8EncodeList (pfx2 ++ [hd])).length := by
                      rw [← hposAdd, BitVec.add_assoc]
                    have htlLen : (utf8EncodeList (hd :: tl)).length - seg.length =
                        (utf8EncodeList tl).length := by omega
                    rw [show (32 : BitVec 64) = 32#64 from rfl, hsegEq, htlLen, hptrAdd] at hmW
                    have hmW' : (bytes (dst + 32#64) (utf8EncodeList (pfx2 ++ [hd])) ⋆
                        region (dst + 32#64 +
                          BitVec.ofNat 64 (utf8EncodeList (pfx2 ++ [hd])).length)
                          (utf8EncodeList tl).length ⋆ rest2) mW := by
                      rw [hApp']
                      exact sep_cast hmW (by ac_rfl)
                    have hposAdd' : BitVec.ofNat 64 (utf8EncodeList pfx2).length +
                        BitVec.ofNat 64 (utf8EncodeBytes ((hd >>> 1) &&&
                          (4294967295 : BitVec 64)).toNat).length =
                        BitVec.ofNat 64 (utf8EncodeList (pfx2 ++ [hd])).length := hposAdd
                    rw [hposAdd']
                    exact hL2 tl.length (nxt,
                      BitVec.ofNat 64 (utf8EncodeList (pfx2 ++ [hd])).length, ()) mW
                      (by rw [← hn2]; simp)
                      ⟨pfx2 ++ [hd], tl, by rw [← hsp2]; simp, rfl, htl, rfl, hmW'⟩)
             · obtain ⟨_, hnil2⟩ := hand2.2 hcur2
               subst hnil2
               rw [List.append_nil] at hsp2
               rw [hsp2] at hmL2
               dsimp only [rest2] at hmL2
               simp only [utf8EncodeList, List.length_nil, region_zero, sep_emp] at hmL2
               let rObj := mkStrObj dst 1#32 (bs.length + 1) bs (cps.length % 2 ^ 64)
               have hcanR : StrCanon rObj :=
                 mkStrObj_canon hdst0 hdst8 (by decide) (Nat.le_refl _) hltMax
                   (Nat.mod_lt _ (by decide))
               have hmObj : (rtC0Inv rt st1 ⋆ lcnfHeap objs ⋆ lcnfObjMem rObj ⋆ R) mL2 := by
                 have hparts : (cell64 dst strHeaderWord ⋆
                     cell64 (dst + 8#64) (BitVec.ofNat 64 (bs.length + 1)) ⋆
                     cell64 (dst + 16#64) (BitVec.ofNat 64 (bs.length + 1)) ⋆
                     cell64 (dst + 24#64) (BitVec.ofNat 64 (cps.length % 2 ^ 64)) ⋆
                     bytes (dst + 32#64) bs ⋆
                     bytes (dst + 32#64 + BitVec.ofNat 64 bs.length) [(0 : UInt8)] ⋆
                     region (dst + 32#64 + BitVec.ofNat 64 bs.length + 1#64)
                       (strAllocBytes (bs.length + 1) - (32 + bs.length + 1)) ⋆
                     (rtC0Inv rt st1 ⋆ lcnfHeap objs ⋆ R)) mL2 := by
                   dsimp only [bs] at hmL2 ⊢
                   rw [show BitVec.ofNat 64 (utf8EncodeList cps).length + 1#64 =
                       BitVec.ofNat 64 ((utf8EncodeList cps).length + 1) from
                     (BitVec.ofNat_add _ 1).symm,
                     show BitVec.ofNat 64 cps.length = BitVec.ofNat 64 (cps.length % 2 ^ 64) from
                       BitVec.eq_of_toNat_eq (by simp [BitVec.toNat_ofNat])] at hmL2
                   exact sep_cast hmL2 (by ac_rfl)
                 exact sep_cast (mkStrObj_mem_of_parts hltMax (Nat.le_refl _) hparts) (by ac_rfl)
               r2b_steps
               all_goals first
                 | (exfalso; exact hcur2 (by assumption))
                 | (r2b_call rtR2bEnv_r2_dec_obj
                    dsimp only [r2DecObjSpec, vals, Tup.map, Arg.val]
                    by_cases hcs1 : cs = 1#64
                    · subst hcs1
                      rw [ite_eq_left (Or.inr (by decide))]
                      r2b_steps
                      exact hk dst st1 objs mL2 hdst0 hdst8 hpr1 hrem1 hcanR
                        (by simp only [DecObjRel, ite_eq_left (Or.inr (by decide :
                          (1#64 &&& 1#64 : BitVec 64) ≠ 0#64))])
                        (sep_cast hmObj (by ac_rfl))
                    · have hnull : ¬ (cs = 0#64 ∨ (cs &&& 1#64) ≠ 0#64) := by
                        obtain ⟨o, hmem, ha, hrc⟩ := hcsPre hcs1
                        have hwo := hwfObjs o hmem
                        intro hbad
                        rcases hbad with h0 | h1
                        · exact hwo.1 (ha ▸ h0)
                        · exact h1 (bv64_and1_zero_of_mod8 (ha ▸ hwo.2.1))
                      rw [ite_eq_right hnull]
                      obtain ⟨o, hmem, ha, hrc⟩ := hcsPre hcs1
                      refine ⟨st1, objs, lcnfObjMem rObj ⋆ R, ⟨o, hmem, ha, fun h1 => ?_⟩,
                        hwfObjs, sep_cast hmObj (by ac_rfl),
                        fun st2 objs' m2 hpr2 hrem2 hdec hm2 => ?_⟩
                      · rw [RtC0State.workCap_eq_of_preservesMeta hpr1]; exact hrc h1
                      · r2b_steps
                        exact hk dst st2 objs' m2 hdst0 hdst8 (hpr1.trans hpr2) (by omega)
                          hcanR hdec (sep_cast hm2 (by ac_rfl)))
           · intro J2 hJ2
             exact @hJ2 cps.length (cs, 0#64, ()) m1
               ⟨[], cps, rfl, rfl, hlist, rfl, (by
                 dsimp only [rest2, bs]
                 simp only [utf8EncodeList, List.length_nil]
                 rw [bytes_nil_eq, emp_sep, BitVec.add_zero]
                 exact sep_cast hm1 (by ac_rfl))⟩)
  · intro J1 hJ1
    exact @hJ1 cps.length (0#64, 0#64, cs, ()) m
      ⟨rfl, [], cps, rfl, rfl, hlist, by unfold strMaxCap; decide, rfl, rfl⟩

/-! ## 4. `lcnf_ba_data` WP Proof -/

theorem lcnf_ba_data_wp :
    ∀ xs m Q X, lcnfBaDataSpec xs m Q X → Func.wp rtR2bEnv lcnf_ba_data_body xs m Q X := by
  intro ⟨rt, ba, ⟨⟩⟩ m Q X hPre
  dsimp only [Func.wp, lcnf_ba_data_body, lcnfBaDataSpec] at hPre ⊢
  rcases hPre with ⟨st, baObj, objs, R, hmem, ha, hcan, hwfObjs, hrc1Ok, hm, hPost⟩
  let n := baObj.scalarData.length
  have hcapMax : baObj.cap ≤ 268435416 := by
    have := hcan.2.2.2.2.2.2.2.2; unfold baMaxCap at *; omega
  have hnLeCap : n ≤ baObj.cap := by
    have h1 := hcan.2.2.2.2.2.2.1; have h2 := hcan.2.2.2.2.2.2.2.1; omega
  have hn64 : n < 2 ^ 64 := by omega
  have hnTo : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64]
  obtain ⟨kB, hkB, hobjB⟩ := List.getElem_of_mem hmem
  have hfocusB := lcnfHeap_focus_obj hkB hobjB
  have hloadSz : loadVal m i64 (ba + 8#64) = some (BitVec.ofNat 64 n) := by
    have hmB : (lcnfObjMem baObj ⋆ (lcnfHeap (objs.take kB) ⋆ lcnfHeap (objs.drop (kB + 1)) ⋆
        rtC0Inv rt st ⋆ R)) m := by
      rw [hfocusB] at hm; exact sep_cast hm (by ac_rfl)
    rw [← ha]
    exact ba_load_sz hcan hmB
  r2b_steps
  apply wp_load_of hloadSz
  r2b_steps
  · have hcmp : (33554428#64 : BitVec 64) < BitVec.ofNat 64 n := by assumption
    have h33 : (33554428#64 : BitVec 64).toNat = 33554428 := rfl
    rw [BitVec.lt_def, h33, hnTo] at hcmp
    have hgt : arrMaxCap < n := by unfold arrMaxCap; exact hcmp
    rw [ite_eq_left hgt] at hPost
    exact hPost
  · have hcmpF : ¬ (33554428#64 : BitVec 64) < BitVec.ofNat 64 n := by assumption
    have hle : n ≤ arrMaxCap := by
      have h33 : (33554428#64 : BitVec 64).toNat = 33554428 := rfl
      rw [BitVec.lt_def, h33, hnTo] at hcmpF; unfold arrMaxCap; exact Nat.not_lt.mp hcmpF
    rw [ite_eq_right (Nat.not_lt.mpr hle)] at hPost
    rcases hPost with ⟨hav, hk⟩
    r2b_call rtR2bEnv_r2_alloc_array
    dsimp only [r2AllocArraySpec, vals, Tup.map, Arg.val]
    rw [hnTo, ite_eq_left ⟨Nat.le_refl _, hle⟩]
    refine ⟨st, lcnfHeap objs ⋆ R, hav, sep_cast hm (by ac_rfl),
      fun arr st1 m1 harr0 harr8 hpr1 hrem1 _ hm1 => ?_⟩
    try dsimp only
    refine wp_loop_group
      (fun rem (xs : Tup Val [i64]) mL =>
        xs.1.toNat ≤ n ∧
        n - xs.1.toNat = rem ∧
        (rtC0Inv rt st1 ⋆ cell64 arr arrHeaderWord ⋆
          cell64 (arr + 8#64) (BitVec.ofNat 64 n) ⋆
          cell64 (arr + 16#64) (BitVec.ofNat 64 n) ⋆
          array64 (arr + 24#64)
            ((baObj.scalarData.take xs.1.toNat).map (fun b => boxNat b.toNat)) ⋆
          region (arr + 24#64 + BitVec.ofNat 64 (8 * xs.1.toNat)) (8 * (n - xs.1.toNat)) ⋆
          lcnfHeap objs ⋆ R) mL) ?_ ?_
    · intro J rem ⟨i, ⟨⟩⟩ mL hL ⟨hiLe, hremEq, hmL⟩
      by_cases hilt : i.toNat < n
      · have hcmpT : i < BitVec.ofNat 64 n := by rw [BitVec.lt_def, hnTo]; exact hilt
        have h8i64 : 8 * i.toNat < 2 ^ 64 := by unfold arrMaxCap at hle; omega
        have hmulEq : (8#64 : BitVec 64) * i = BitVec.ofNat 64 (8 * i.toNat) := by
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_mul, BitVec.toNat_ofNat,
            show (8#64 : BitVec 64).toNat = 8 from rfl]
        have h0 : (lcnfObjMem baObj ⋆
            (lcnfHeap (objs.take kB) ⋆ lcnfHeap (objs.drop (kB + 1)) ⋆
              rtC0Inv rt st1 ⋆ cell64 arr arrHeaderWord ⋆
              cell64 (arr + 8#64) (BitVec.ofNat 64 n) ⋆
              cell64 (arr + 16#64) (BitVec.ofNat 64 n) ⋆
              array64 (arr + 24#64)
                ((baObj.scalarData.take i.toNat).map (fun b => boxNat b.toNat)) ⋆
              region (arr + 24#64 + BitVec.ofNat 64 (8 * i.toNat)) (8 * (n - i.toNat)) ⋆
              R)) mL := by
          rw [hfocusB] at hmL; exact sep_cast hmL (by ac_rfl)
        rw [lcnfObjMem_sarray_elim_eq hcan, ha, sep_assoc] at h0
        have hloadB : loadVal mL i8 (ba + 24#64 + i) =
            some (BitVec.ofNat 8 baObj.scalarData[i.toNat].toNat) :=
          r2_c0_load_bytes_add24 h0 hilt (Nat.le_of_lt hn64)
        r2b_steps
        apply wp_load_of hloadB
        r2b_steps
        have hregFit : 8 * (n - i.toNat) ≤ 2 ^ 64 := by
          unfold arrMaxCap at hle; omega
        obtain ⟨w0, hmPop⟩ := region_pop_cell64 (by omega : 8 ≤ 8 * (n - i.toNat))
          hregFit (sep_cast hmL (by ac_rfl) :
            (region (arr + 24#64 + BitVec.ofNat 64 (8 * i.toNat)) (8 * (n - i.toNat)) ⋆
              (rtC0Inv rt st1 ⋆ cell64 arr arrHeaderWord ⋆
                cell64 (arr + 8#64) (BitVec.ofNat 64 n) ⋆
                cell64 (arr + 16#64) (BitVec.ofNat 64 n) ⋆
                array64 (arr + 24#64)
                  ((baObj.scalarData.take i.toNat).map (fun b => boxNat b.toNat)) ⋆
                lcnfHeap objs ⋆ R)) mL)
        have hmPop' : (cell64 (arr + 24#64 + 8#64 * i) w0 ⋆
            (region (arr + 24#64 + BitVec.ofNat 64 (8 * i.toNat) + 8#64)
              (8 * (n - i.toNat) - 8) ⋆
              rtC0Inv rt st1 ⋆ cell64 arr arrHeaderWord ⋆
              cell64 (arr + 8#64) (BitVec.ofNat 64 n) ⋆
              cell64 (arr + 16#64) (BitVec.ofNat 64 n) ⋆
              array64 (arr + 24#64)
                ((baObj.scalarData.take i.toNat).map (fun b => boxNat b.toNat)) ⋆
              lcnfHeap objs ⋆ R)) mL := by
          rw [hmulEq]; exact sep_cast hmPop (by ac_rfl)
        let bvVal := (BitVec.setWidth 64
          (BitVec.ofNat 8 baObj.scalarData[i.toNat].toNat) <<<
          (BitVec.signExtend 64 1#32)) ||| 1#64
        apply wp_store64_var hmPop'
        intro m2 hm2
        r2b_steps
        have hi1To : (i + 1#64).toNat = i.toNat + 1 := by
          simp only [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl]
          rw [Nat.mod_eq_of_lt (by omega)]
        have hboxEq : bvVal = boxNat baObj.scalarData[i.toNat].toNat :=
          bv_box_u8_eq baObj.scalarData[i.toNat]
        have htake : (baObj.scalarData.take (i + 1#64).toNat).map
              (fun b => boxNat b.toNat) =
            (baObj.scalarData.take i.toNat).map (fun b => boxNat b.toNat) ++
              [boxNat baObj.scalarData[i.toNat].toNat] := by
          rw [hi1To, List.take_succ_eq_append_getElem hilt, List.map_append,
            List.map_cons, List.map_nil]
        have hlenMap : ((baObj.scalarData.take i.toNat).map
            (fun b => boxNat b.toNat)).length = i.toNat := by
          rw [List.length_map, List.length_take, Nat.min_eq_left (by omega)]
        have hApp := array64_append (arr + 24#64)
          ((baObj.scalarData.take i.toNat).map (fun b => boxNat b.toNat))
          [boxNat baObj.scalarData[i.toNat].toNat]
        rw [hlenMap, ← hmulEq] at hApp
        have hptrNext : arr + 24#64 + BitVec.ofNat 64 (8 * i.toNat) + 8#64 =
            arr + 24#64 + BitVec.ofNat 64 (8 * (i + 1#64).toNat) := by
          rw [hi1To]; apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
          omega
        have hremNext : 8 * (n - i.toNat) - 8 = 8 * (n - (i + 1#64).toNat) := by
          rw [hi1To]; omega
        change (cell64 (arr + 24#64 + 8#64 * i) bvVal ⋆ _) m2 at hm2
        rw [hboxEq, hptrNext, hremNext] at hm2
        have hm2' : (rtC0Inv rt st1 ⋆ cell64 arr arrHeaderWord ⋆
            cell64 (arr + 8#64) (BitVec.ofNat 64 n) ⋆
            cell64 (arr + 16#64) (BitVec.ofNat 64 n) ⋆
            array64 (arr + 24#64)
              ((baObj.scalarData.take (i + 1#64).toNat).map (fun b => boxNat b.toNat)) ⋆
            region (arr + 24#64 + BitVec.ofNat 64 (8 * (i + 1#64).toNat))
              (8 * (n - (i + 1#64).toNat)) ⋆ lcnfHeap objs ⋆ R) m2 := by
          rw [htake, hApp]
          have hcell : cell64 (arr + 24#64 + 8#64 * i)
              (boxNat baObj.scalarData[i.toNat].toNat) =
              array64 (arr + 24#64 + 8#64 * i)
                [boxNat baObj.scalarData[i.toNat].toNat] := by
            simp [array64, sep_emp]
          rw [hcell] at hm2
          exact sep_cast hm2 (by ac_rfl)
        exact hL (n - (i + 1#64).toNat) (i + 1#64, ()) m2
          (by rw [hi1To, ← hremEq]; exact Nat.sub_lt_sub_left hilt (Nat.lt_succ_self _))
          ⟨by rw [hi1To]; exact hilt, rfl, hm2'⟩
      · dsimp only at hiLe
        have hiEq : i.toNat = n := Nat.le_antisymm hiLe (Nat.not_lt.mp hilt)
        have hcmpF' : ¬ i < BitVec.ofNat 64 n := by rw [BitVec.lt_def, hnTo]; exact hilt
        rw [hiEq, Nat.sub_self, Nat.mul_zero, region_zero, List.take_length] at hmL
        simp only [sep_emp] at hmL
        let elems := baObj.scalarData.map (fun b => boxNat b.toNat)
        let arrObj := mkArrObj arr 1#32 n elems
        have helens : elems.length = n := by simp [elems, n]
        have hcanArr : ArrCanon arrObj :=
          mkArrObj_canon harr0 harr8 (by decide) (by rw [helens]; exact Nat.le_refl _) hle
        have hmArr : (rtC0Inv rt st1 ⋆ lcnfHeap objs ⋆ lcnfObjMem arrObj ⋆ R) mL := by
          have hparts : (cell64 arr (mkArrObj arr 1#32 n elems).header ⋆
              cell64 (arr + 8#64) (BitVec.ofNat 64 elems.length) ⋆
              cell64 (arr + 16#64) (BitVec.ofNat 64 n) ⋆
              array64 (arr + 24#64) elems ⋆
              region (arr + BitVec.ofNat 64 (24 + 8 * elems.length))
                (8 * (n - elems.length)) ⋆
              (rtC0Inv rt st1 ⋆ lcnfHeap objs ⋆ R)) mL := by
            rw [helens, Nat.sub_self, Nat.mul_zero, region_zero, sep_emp, mkArrObj_header]
            exact sep_cast hmL (by ac_rfl)
          exact sep_cast (r2b_mkArrObj_mem_of_parts hparts) (by ac_rfl)
        r2b_steps
        r2b_call rtR2bEnv_r2_dec_obj
        dsimp only [r2DecObjSpec, vals, Tup.map, Arg.val]
        have hnotNull : ¬ (ba = 0#64 ∨ (ba &&& 1#64) ≠ 0#64) := by
          simp [ha ▸ hcan.1, ha ▸ bv64_and1_zero_of_mod8 hcan.2.1]
        rw [ite_eq_right hnotNull]
        refine ⟨st1, objs, lcnfObjMem arrObj ⋆ R, ⟨baObj, hmem, ha, fun hrc1 => ?_⟩,
          hwfObjs, sep_cast hmArr (by ac_rfl),
          fun st2 objs' m2 hpr2 hrem2 hdec hm2 => ?_⟩
        · rw [RtC0State.workCap_eq_of_preservesMeta hpr1]; exact hrc1Ok hrc1
        · r2b_steps
          exact hk arr st2 objs' m2 harr0 harr8 (hpr1.trans hpr2) (by omega) hcanArr hdec
            (sep_cast hm2 (by ac_rfl))
    · intro J hJ
      exact @hJ n (0#64, ()) m1
        ⟨by simp, by simp, (by
          simp only [show (0#64 : BitVec 64).toNat = 0 from rfl, Nat.sub_zero, Nat.mul_zero,
            List.take_zero, List.map_nil, array64, BitVec.add_zero]
          exact sep_cast hm1 (by ac_rfl))⟩
where
  lcnfObjMem_sarray_elim_eq {o : LcnfObj} (hc : BaCanon o) :
      lcnfObjMem o =
        (bytes (o.addr + 24#64) o.scalarData ⋆
          (cell64 o.addr o.header ⋆
            cell64 (o.addr + 8#64) (BitVec.ofNat 64 o.arrSize) ⋆
            cell64 (o.addr + 16#64) (BitVec.ofNat 64 o.cap) ⋆
            region (o.addr + BitVec.ofNat 64 (24 + o.scalarData.length))
              (baAllocBytes o.cap - (24 + o.scalarData.length)))) := by
    rw [lcnfObjMem_sarray_eq hc.2.2.2.2.2.1]
    have htb : o.totalBytes = baAllocBytes o.cap := by
      unfold LcnfObj.totalBytes baAllocBytes
      simp [hc.2.2.2.2.2.1, hc.2.2.2.2.1, sarrayTag, arrayTag]
    rw [htb]
    ac_rfl

end LeanQbe.T.LeanLCNF
