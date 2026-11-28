module
public import LeanQbe.T.Examples.Kissat.Proof.Congruence.Inv
public import LeanQbe.T.Examples.Kissat.Src.Congruence

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Congruence

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Congruence
open LeanQbe.T.Examples.Kissat.Proof.Spec LeanQbe.T.Examples.Kissat.Proof.Congruence.Spec
open Kraken.Bedrock2.Test
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Congruence.CongTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Congruence.CongTactics

public section

/-! ### Helper invariants and layout lemmas for `congruence_dense` -/

private theorem fullDenseInvW_to_dense {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hd : FullDenseInvW c F0 F_cur s) : FullDenseInv c F0 s :=
  ⟨⟨hd.1, ⟨F_cur, hd.2.1⟩⟩, hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2.1,
    hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩

private theorem fullDenseInvW_with_tarjan_mark {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hd : FullDenseInvW c F0 F_cur s)
    {tm' : List (BitVec 32)} (htm : tm'.length = 2 * c.max_vars) :
    FullDenseInvW c F0 F_cur
      { core := s.core, scratch := { s.scratch with tarjan_mark := tm' } } :=
  ⟨⟨hd.1.core_ok, { hd.1.scratch_ok with tarjan_mark_len := htm }⟩,
    hd.2.1, hd.2.2.1, hd.2.2.2.1,
    fullExtScratchOk_of_eq hd.2.2.2.2.1 rfl rfl rfl rfl,
    hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩

private theorem fullCongReprInv_of_id (F_cur : List (List Nat)) (nlits : Nat)
    (repr : List (BitVec 32)) (hlen : nlits ≤ repr.length)
    (hid : ∀ l, l < nlits → (repr[l]?.getD 0#32).toNat = l) :
    FullCongReprInv F_cur nlits repr :=
  ⟨⟨hlen, fun l hl => by rw [hid l hl]; exact Nat.le_refl _⟩,
    fun l hl => by rw [hid l hl]; exact LitEquiv.refl _ _⟩

private theorem bv64_sext_one : BitVec.signExtend 64 1#32 = 1#64 := by decide

private theorem bv32_trunc_eq_ofNat (x : BitVec 64) (hx : x.toNat < 2 ^ 32) :
    BitVec.setWidth 32 x = BitVec.ofNat 32 x.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]

private theorem bv64_sub_toNat {a b : BitVec 64} (h : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat :=
  BitVec.toNat_sub_of_le (BitVec.le_def.mpr h)

private theorem pow2_le_self_of_le20 {p : Nat} (hp : p ≤ 20) : 2 ^ p ≤ 1048576 :=
  le_trans (Nat.pow_le_pow_right (by omega) hp) (by decide)

private theorem cong_ht_bkt_bound {g_len scr_cap v547 : Nat}
    (hscr : 256 ≤ scr_cap) (hgl_le : g_len ≤ scr_cap / 2)
    (hv_ge : 64 ≤ v547) (hv_top : v547 = 64 ∨ 2 * v547 ≤ scr_cap - g_len) :
    v547 + 56 ≤ scr_cap - g_len := by
  rcases hv_top with rfl | _ <;> omega

private theorem cong_bkt_mul16_bound {v554 v552 : Nat}
    (hv_ge : 16 ≤ v554) (hmul : 16 * v554 ≤ v552) : 3 * v554 + 8 ≤ v552 := by
  omega

private theorem congCtrlLayout_mk {c : FullCfg} {scr : List (BitVec 32)}
    {g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz p : Nat}
    (hctrl_lt : ctrl_off < c.scratch_cap) (hctrl8 : ctrl_off + 8 ≤ q_off)
    (hgl_ctrl : g_len ≤ ctrl_off) (hgl_max : g_len ≤ 16777216)
    (h0 : scr[ctrl_off]? = some (BitVec.ofNat 32 occ_bkt))
    (h1 : scr[ctrl_off + 1]? = some (BitVec.ofNat 32 bkt_off))
    (h2 : scr[ctrl_off + 2]? = some (BitVec.ofNat 32 inq_off))
    (h3 : scr[ctrl_off + 3]? = some (BitVec.ofNat 32 q_off))
    (h4 : scr[ctrl_off + 4]? = some 0#32) (h5 : scr[ctrl_off + 5]? = some 0#32)
    (h6 : scr[ctrl_off + 6]? = some (BitVec.ofNat 32 ht_off))
    (h7 : scr[ctrl_off + 7]? = some (BitVec.ofNat 32 ht_sz))
    (hp1 : 1 ≤ p) (hp20 : p ≤ 20) (hocc : occ_bkt = 2 ^ p)
    (hocc_max : occ_bkt ≤ congOccBktMax) (hht_pos : 0 < ht_sz)
    (hq_inq : q_off + occ_bkt ≤ inq_off) (hinq_bkt : inq_off + occ_bkt ≤ bkt_off)
    (hbkt_ht : bkt_off + occ_bkt ≤ ht_off) (hht_cap : ht_off + ht_sz ≤ c.scratch_cap) :
    CongCtrlLayout c scr g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz := by
  have hocc_pos : 0 < occ_bkt := by rw [hocc]; exact Nat.pow_pos (by omega)
  refine ⟨hctrl_lt, by omega, hgl_ctrl, hgl_max, by simp [h0], by simp [h1], by simp [h2],
    by simp [h3], by simp [h6], by simp [h7], hocc_pos, hocc_max, ⟨p, hp1, hp20, hocc⟩, hht_pos,
    hctrl8, hq_inq, hinq_bkt, hbkt_ht, hht_cap, by simp [h4]; exact hocc_pos,
    by simp [h5], fun k hk => by simp [h5] at hk⟩

private theorem dense_ctrl_setup_ok {maxA : Nat} {F_cur : List (List Nat)} {c : FullCfg}
    {cv g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz p : Nat}
    {scr0 scr : List (BitVec 32)}
    {w0 w1 w2 w3 w6 w7 : BitVec 32}
    (hlen : scr.length = c.scratch_cap)
    (hpref : ∀ idx, idx < g_len → scr[idx]? = scr0[idx]?)
    (hht_clr : ∀ k, k < ht_sz → scr[ht_off + k]? = some 4294967295#32)
    (hctrl_lt : ctrl_off < c.scratch_cap) (hctrl8 : ctrl_off + 8 ≤ q_off)
    (hgl_ctrl : g_len ≤ ctrl_off) (hgl_max : g_len ≤ 16777216)
    (hw0 : w0 = BitVec.ofNat 32 occ_bkt) (hw1 : w1 = BitVec.ofNat 32 bkt_off)
    (hw2 : w2 = BitVec.ofNat 32 inq_off) (hw3 : w3 = BitVec.ofNat 32 q_off)
    (hw6 : w6 = BitVec.ofNat 32 ht_off) (hw7 : w7 = BitVec.ofNat 32 ht_sz)
    (hp1 : 1 ≤ p) (hp20 : p ≤ 20) (hocc : occ_bkt = 2 ^ p)
    (hocc_max : occ_bkt ≤ congOccBktMax) (hht_pos : 0 < ht_sz)
    (hq_inq : q_off + occ_bkt ≤ inq_off) (hinq_bkt : inq_off + occ_bkt ≤ bkt_off)
    (hbkt_ht : bkt_off + occ_bkt ≤ ht_off) (hht_cap : ht_off + ht_sz ≤ c.scratch_cap) :
    let scr' :=
      (((((((scr.set ctrl_off w0).set (ctrl_off + 1) w1).set (ctrl_off + 2) w2).set
        (ctrl_off + 3) w3).set (ctrl_off + 4) 0#32).set (ctrl_off + 5) 0#32).set
        (ctrl_off + 6) w6).set (ctrl_off + 7) w7
    scr'.length = c.scratch_cap ∧
      CongCtrlLayout c scr' g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz ∧
      (∀ idx, idx < g_len → scr'[idx]? = scr0[idx]?) ∧
      CongHtInv maxA F_cur cv scr0 scr' g_len ht_off ht_sz := by
  intro scr'
  have hlen' : scr'.length = c.scratch_cap := by simp [scr', hlen]
  have hc8_lt : ctrl_off + 8 ≤ c.scratch_cap := by omega
  have hget : ∀ (k : Nat), k < 8 →
      scr'[ctrl_off + k]? =
        some (match k with
          | 0 => w0 | 1 => w1 | 2 => w2 | 3 => w3
          | 4 => 0#32 | 5 => 0#32 | 6 => w6 | _ => w7) := by
    intro k hk
    have hlt : ∀ m, m < 7 →
        ctrl_off + m < scr.length := fun m hm => by rw [hlen]; omega
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    · simp only [scr', Nat.add_zero]
      repeat first
        | rw [List.getElem?_set_ne (by omega)]
        | rw [List.getElem?_set_self (by simp [hlen]; omega)]
  have hlay := congCtrlLayout_mk hctrl_lt hctrl8 hgl_ctrl hgl_max
    (hw0 ▸ hget 0 (by omega)) (hw1 ▸ hget 1 (by omega)) (hw2 ▸ hget 2 (by omega))
    (hw3 ▸ hget 3 (by omega)) (hget 4 (by omega)) (hget 5 (by omega))
    (hw6 ▸ hget 6 (by omega)) (hw7 ▸ hget 7 (by omega))
    hp1 hp20 hocc hocc_max hht_pos hq_inq hinq_bkt hbkt_ht hht_cap
  have hpref' : ∀ idx, idx < g_len → scr'[idx]? = scr0[idx]? := by
    intro idx hidx; simp only [scr']
    repeat rw [List.getElem?_set_ne (by omega)]
    exact hpref idx hidx
  have hht' : CongHtInv maxA F_cur cv scr0 scr' g_len ht_off ht_sz := by
    refine congHtInv_clear (fun k hk => ?_)
    simp only [scr']
    repeat rw [List.getElem?_set_ne (by omega)]
    exact hht_clr k hk
  exact ⟨hlen', hlay, hpref', hht'⟩

/-! ### Pure step helpers for `full_congruence_dense_wp` -/

private theorem bv64_add_imm_lt (x : BitVec 64) (k : Nat) (hk : k < 2 ^ 64)
    (h : x.toNat + k < 2 ^ 64) : (x + OfNat.ofNat k).toNat = x.toNat + k := by
  change (x + BitVec.ofNat 64 k).toNat = x.toNat + k
  exact bv64_addk_lt_of hk h

private theorem dense_tmk_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {sk : FullState} {cv : Nat} {k : BitVec 64}
    (hd : FullDenseInvW c F0 F_cur sk) (_hcv_eq : sk.core.cur_vars = cv)
    (hc : k.toNat < cv % 2 ^ 64) (hcv_max : cv ≤ c.max_vars) :
    k.toNat < cv ∧ k.toNat < sk.scratch.tarjan_mark.length ∧
      (k + 1#64).toNat = k.toNat + 1 ∧
      FullDenseInvW c F0 F_cur
        { core := sk.core, scratch :=
          { sk.scratch with tarjan_mark := sk.scratch.tarjan_mark.set k.toNat 0#32 } } := by
  have hmax31 : c.max_vars < 2 ^ 31 := Nat.lt_trans c.hmaxv (by decide)
  have hk_lt : k.toNat < cv := Nat.lt_of_lt_of_le hc (Nat.mod_le _ _)
  have htm : k.toNat < sk.scratch.tarjan_mark.length := by
    rw [hd.1.scratch_ok.tarjan_mark_len]; omega
  exact ⟨hk_lt, htm, bv64_add1_lt (by omega),
    fullDenseInvW_with_tarjan_mark hd (tm' := sk.scratch.tarjan_mark.set k.toNat 0#32)
      (by rw [List.length_set, hd.1.scratch_ok.tarjan_mark_len])⟩

private theorem dense_ht_sz_step {v561 v547 : BitVec 64} {g_len : Nat}
    (hpos : 0 < v561.toNat) (_hlt : v561.toNat < g_len) (hv_le : v561.toNat ≤ v547.toNat)
    (hv547_le : v547.toNat ≤ 1048576)
    (hle2 : (v561 <<< BitVec.signExtend 64 1#32).toNat ≤ v547.toNat) :
    v547.toNat - (v561 <<< 1#64).toNat < v547.toNat - v561.toNat ∧
      0 < (v561 <<< 1#64).toNat ∧ (v561 <<< 1#64).toNat ≤ v547.toNat ∧
      (v561 <<< 1#64).toNat ≤ 1048576 := by
  have h2 : (v561 <<< BitVec.signExtend 64 1#32).toNat = 2 * v561.toNat := by
    rw [bv64_sext_one]; exact bv64_shl1_lt (by omega)
  have h2' : (v561 <<< 1#64).toNat = 2 * v561.toNat := bv64_shl1_lt (by omega)
  omega

private theorem dense_occ_step {cap v g p : Nat} {v554 : BitVec 64}
    (hp4 : 4 ≤ p) (hp20 : p ≤ 20) (hvp : v554.toNat = 2 ^ p) (hv_ge : 16 ≤ v554.toNat)
    (hv_max : v554.toNat ≤ congOccBktMax) (hcap : cap < 2 ^ 64)
    (hv_3 : 3 * v554.toNat + 8 ≤ cap - v - g)
    (hsh : (v554 <<< BitVec.signExtend 64 1#32).toNat ≤ 1048576)
    (hmul : (2 * v554.toNat % 2 ^ 64 * (16 : BitVec 64).toNat) % 2 ^ 64 ≤
      (2 ^ 64 - g + (2 ^ 64 - v + cap)) % 2 ^ 64) :
    1048576 - (v554 <<< 1#64).toNat < 1048576 - v554.toNat ∧
      (∃ p', 4 ≤ p' ∧ p' ≤ 20 ∧ (v554 <<< 1#64).toNat = 2 ^ p') ∧
      16 ≤ (v554 <<< 1#64).toNat ∧ (v554 <<< 1#64).toNat ≤ congOccBktMax ∧
      3 * (v554 <<< 1#64).toNat + 8 ≤ cap - v - g := by
  unfold congOccBktMax at hv_max ⊢
  have hsh1 : (v554 <<< BitVec.signExtend 64 1#32).toNat = 2 * v554.toNat := by
    rw [bv64_sext_one]; exact bv64_shl1_lt (by omega)
  have h2le : 2 * v554.toNat ≤ 1048576 := by omega
  have hsh' : (v554 <<< 1#64).toNat = 2 * v554.toNat := bv64_shl1_lt (by omega)
  have h16le : 16 * (2 * v554.toNat) ≤ cap - v - g := by
    rw [show (16 : BitVec 64).toNat = 16 from by decide,
      Nat.mod_eq_of_lt (by omega : 2 * v554.toNat < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : 2 * v554.toNat * 16 < 2 ^ 64)] at hmul
    have hrem : (2 ^ 64 - g + (2 ^ 64 - v + cap)) % 2 ^ 64 = cap - v - g := by omega
    omega
  have hp1_le : p + 1 ≤ 20 := by
    rcases (by omega : p ≤ 19 ∨ p = 20) with _ | rfl
    · omega
    · rw [hvp, (by decide : 2 ^ 20 = 1048576)] at h2le; omega
  exact ⟨by omega, ⟨p + 1, by omega, hp1_le, by rw [hsh', hvp, Nat.pow_succ']⟩,
    by omega, by omega, cong_bkt_mul16_bound (by omega) (by rw [hsh']; exact h16le)⟩

private theorem dense_ht_step {cap g p547 : Nat} {v547 : BitVec 64}
    (hp6 : 6 ≤ p547) (hp20 : p547 ≤ 20) (hvp : v547.toNat = 2 ^ p547)
    (hv_ge : 64 ≤ v547.toNat) (hv_le : v547.toNat ≤ 1048576) (hcap : cap < 2 ^ 64)
    (hg : g ≤ cap) (hlt : v547.toNat < 1048576)
    (hmul : (v547.toNat * (4 : BitVec 64).toNat) % 2 ^ 64 ≤ (2 ^ 64 - g + cap) % 2 ^ 64) :
    1048576 - (v547 <<< 1#64).toNat < 1048576 - v547.toNat ∧
      (∃ p', 6 ≤ p' ∧ p' ≤ 20 ∧ (v547 <<< 1#64).toNat = 2 ^ p') ∧
      64 ≤ (v547 <<< 1#64).toNat ∧ (v547 <<< 1#64).toNat ≤ 1048576 ∧
      ((v547 <<< 1#64).toNat = 64 ∨ 2 * (v547 <<< 1#64).toNat ≤ cap - g) := by
  have h4le : 4 * v547.toNat ≤ cap - g := by
    rw [show (4 : BitVec 64).toNat = 4 from by decide,
      Nat.mod_eq_of_lt (by omega : v547.toNat * 4 < 2 ^ 64)] at hmul
    have hrem : (2 ^ 64 - g + cap) % 2 ^ 64 = cap - g := by omega
    omega
  have hp1_le : p547 + 1 ≤ 20 := by
    rcases (by omega : p547 ≤ 19 ∨ p547 = 20) with _ | rfl
    · omega
    · rw [hvp, (by decide : 2 ^ 20 = 1048576)] at hlt; omega
  have hsh' : (v547 <<< 1#64).toNat = 2 * v547.toNat := bv64_shl1_lt (by omega)
  have hpow : (v547 <<< 1#64).toNat = 2 ^ (p547 + 1) := by rw [hsh', hvp, Nat.pow_succ']
  refine ⟨by omega, ⟨p547 + 1, by omega, hp1_le, hpow⟩, by omega,
    by rw [hpow]; exact pow2_le_self_of_le20 hp1_le, Or.inr (by omega)⟩

private theorem dense_hv551_init {cap : Nat} {v547 g_len : BitVec 64}
    (hcap : cap < 2 ^ 64) (h56 : v547.toNat + 56 ≤ cap - g_len.toNat) :
    (BitVec.ofNat 64 cap - v547).toNat = cap - v547.toNat ∧
      (BitVec.ofNat 64 cap - v547 - g_len).toNat = cap - v547.toNat - g_len.toNat ∧
      3 * (16#64 : BitVec 64).toNat + 8 ≤ cap - v547.toNat - g_len.toNat := by
  have h551 : (BitVec.ofNat 64 cap - v547).toNat = cap - v547.toNat := by
    rw [bv64_sub_toNat (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcap]; omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcap]
  have h552 : (BitVec.ofNat 64 cap - v547 - g_len).toNat = cap - v547.toNat - g_len.toNat := by
    rw [bv64_sub_toNat (by rw [h551]; omega), h551]
  exact ⟨h551, h552, by rw [show (16#64 : BitVec 64).toNat = 16 from rfl]; omega⟩

private theorem dense_sub_chain {cap : Nat} {v547 v554 g_len : BitVec 64}
    (hv551 : (BitVec.ofNat 64 cap - v547).toNat = cap - v547.toNat)
    (hv3 : 3 * v554.toNat + 8 ≤ cap - v547.toNat - g_len.toNat) :
    let v551 := BitVec.ofNat 64 cap - v547
    let v556 := v551 - v554
    let v557 := v556 - v554
    let v558 := v557 - v554
    let v559 := v558 - (8 : BitVec 64)
    v556.toNat = cap - v547.toNat - v554.toNat ∧
      v557.toNat = cap - v547.toNat - 2 * v554.toNat ∧
      v558.toNat = cap - v547.toNat - 3 * v554.toNat ∧
      v559.toNat = cap - v547.toNat - 3 * v554.toNat - 8 := by
  intro v551 v556 v557 v558 v559
  have h556 : v556.toNat = cap - v547.toNat - v554.toNat := by
    rw [bv64_sub_toNat (by rw [hv551]; omega), hv551]
  have h557 : v557.toNat = cap - v547.toNat - 2 * v554.toNat := by
    rw [bv64_sub_toNat (by rw [h556]; omega), h556]; omega
  have h558 : v558.toNat = cap - v547.toNat - 3 * v554.toNat := by
    rw [bv64_sub_toNat (by rw [h557]; omega), h557]; omega
  have h559 : v559.toNat = cap - v547.toNat - 3 * v554.toNat - 8 := by
    rw [bv64_sub_toNat (by rw [h558, show (8 : BitVec 64).toNat = 8 from rfl]; omega), h558]
    rfl
  exact ⟨h556, h557, h558, h559⟩

private theorem dense_ht_clr_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {sk : FullState} {scr0 : List (BitVec 32)} {v547 v551 v554 v561 g_len k : BitVec 64}
    (hdsk : FullDenseInvW c F0 F_cur sk) (hscr_lt31 : c.scratch_cap < 2 ^ 31)
    (hv551 : v551.toNat = c.scratch_cap - v547.toNat) (hle561 : v561.toNat ≤ v547.toNat)
    (hv554_3 : 3 * v554.toNat + 8 ≤ c.scratch_cap - v547.toNat - g_len.toNat)
    (hk_lt : k.toNat < v561.toNat)
    (hpref_k : ∀ idx, idx < g_len.toNat → sk.scratch.scratch_buf[idx]? = scr0[idx]?)
    (hht_k : ∀ t, t < k.toNat → sk.scratch.scratch_buf[v551.toNat + t]? = some 4294967295#32) :
    let scr' := sk.scratch.scratch_buf.set (v551 + k).toNat 4294967295#32
    (v551 + k).toNat = v551.toNat + k.toNat ∧
      (v551 + k).toNat < sk.scratch.scratch_buf.length ∧
      (k + 1#64).toNat = k.toNat + 1 ∧
      v561.toNat - (k + 1#64).toNat < v561.toNat - k.toNat ∧
      (k + 1#64).toNat ≤ v561.toNat ∧
      FullDenseInvW c F0 F_cur
        { core := sk.core, scratch := { sk.scratch with scratch_buf := scr' } } ∧
      (∀ idx, idx < g_len.toNat → scr'[idx]? = scr0[idx]?) ∧
      (∀ t, t < (k + 1#64).toNat → scr'[v551.toNat + t]? = some 4294967295#32) := by
  intro scr'
  have hk_idx : (v551 + k).toNat = v551.toNat + k.toNat := by
    rw [BitVec.toNat_add, hv551]; exact Nat.mod_eq_of_lt (by omega)
  have hk_len : (v551 + k).toNat < sk.scratch.scratch_buf.length := by
    rw [hdsk.1.scratch_ok.scratch_buf_len, hk_idx, hv551]; omega
  have hk1 : (k + 1#64).toNat = k.toNat + 1 := bv64_add1_lt (by omega)
  refine ⟨hk_idx, hk_len, hk1, by omega, by omega,
    fullDenseInvW_with_scr hdsk (scr' := scr')
      (by rw [List.length_set, hdsk.1.scratch_ok.scratch_buf_len]),
    fun idx hidx => ?_, fun t ht => ?_⟩
  · dsimp only [scr']
    rw [List.getElem?_set_ne (by rw [hk_idx, hv551]; omega)]
    exact hpref_k idx hidx
  · dsimp only [scr']; by_cases htk : t = k.toNat
    · subst htk; rw [← hk_idx, List.getElem?_set_self hk_len]
    · rw [List.getElem?_set_ne (by rw [hk_idx]; omega)]; exact hht_k t (by omega)

private theorem dense_ctrl_addrs {cap len : Nat} {v547 v554 v559 g_len : BitVec 64}
    (hlen : len = cap) (hcap : cap < 2 ^ 31)
    (hv559 : v559.toNat = cap - v547.toNat - 3 * v554.toNat - 8)
    (hv3 : 3 * v554.toNat + 8 ≤ cap - v547.toNat - g_len.toNat) :
    (v559.toNat < len ∧
      (v559 + OfNat.ofNat 1).toNat < len ∧ (v559 + OfNat.ofNat 2).toNat < len ∧
      (v559 + OfNat.ofNat 3).toNat < len ∧ (v559 + OfNat.ofNat 4).toNat < len ∧
      (v559 + OfNat.ofNat 5).toNat < len ∧ (v559 + OfNat.ofNat 6).toNat < len ∧
      (v559 + OfNat.ofNat 7).toNat < len) ∧
      (v559 + OfNat.ofNat 1).toNat = v559.toNat + 1 ∧
      (v559 + OfNat.ofNat 2).toNat = v559.toNat + 2 ∧
      (v559 + OfNat.ofNat 3).toNat = v559.toNat + 3 ∧
      (v559 + OfNat.ofNat 4).toNat = v559.toNat + 4 ∧
      (v559 + OfNat.ofNat 5).toNat = v559.toNat + 5 ∧
      (v559 + OfNat.ofNat 6).toNat = v559.toNat + 6 ∧
      (v559 + OfNat.ofNat 7).toNat = v559.toNat + 7 := by
  have hc1 := bv64_add_imm_lt v559 1 (by decide) (by rw [hv559]; omega)
  have hc2 := bv64_add_imm_lt v559 2 (by decide) (by rw [hv559]; omega)
  have hc3 := bv64_add_imm_lt v559 3 (by decide) (by rw [hv559]; omega)
  have hc4 := bv64_add_imm_lt v559 4 (by decide) (by rw [hv559]; omega)
  have hc5 := bv64_add_imm_lt v559 5 (by decide) (by rw [hv559]; omega)
  have hc6 := bv64_add_imm_lt v559 6 (by decide) (by rw [hv559]; omega)
  have hc7 := bv64_add_imm_lt v559 7 (by decide) (by rw [hv559]; omega)
  exact ⟨⟨by rw [hlen, hv559]; omega,
    by rw [hc1, hlen, hv559]; omega, by rw [hc2, hlen, hv559]; omega,
    by rw [hc3, hlen, hv559]; omega, by rw [hc4, hlen, hv559]; omega,
    by rw [hc5, hlen, hv559]; omega, by rw [hc6, hlen, hv559]; omega,
    by rw [hc7, hlen, hv559]; omega⟩, hc1, hc2, hc3, hc4, hc5, hc6, hc7⟩

private theorem dense_ctrl_bundle {maxA : Nat} {F_cur : List (List Nat)} {c : FullCfg}
    {cv p : Nat} {scr0 scr : List (BitVec 32)}
    {g_len v32 v547 v551 v554 v556 v557 v558 v559 v561 k : BitVec 64}
    (hlen : scr.length = c.scratch_cap) (hscr_lt31 : c.scratch_cap < 2 ^ 31)
    (hpref : ∀ idx, idx < g_len.toNat → scr[idx]? = scr0[idx]?)
    (hht_k : ∀ t, t < k.toNat → scr[v551.toNat + t]? = some 4294967295#32)
    (hk_ge : ¬k.toNat < v561.toNat) (hgl_le : g_len.toNat ≤ v32.toNat)
    (hv32_cap : v32.toNat ≤ 16777215)
    (hp4 : 4 ≤ p) (hp20 : p ≤ 20) (hv554_p : v554.toNat = 2 ^ p)
    (hv554_max : v554.toNat ≤ congOccBktMax)
    (hv554_3 : 3 * v554.toNat + 8 ≤ c.scratch_cap - v547.toNat - g_len.toNat)
    (hpos561 : 0 < v561.toNat) (hle561 : v561.toNat ≤ v547.toNat)
    (hmax561 : v561.toNat ≤ 1048576)
    (hv551 : v551.toNat = c.scratch_cap - v547.toNat)
    (hv556 : v556.toNat = c.scratch_cap - v547.toNat - v554.toNat)
    (hv557 : v557.toNat = c.scratch_cap - v547.toNat - 2 * v554.toNat)
    (hv558 : v558.toNat = c.scratch_cap - v547.toNat - 3 * v554.toNat)
    (hv559 : v559.toNat = c.scratch_cap - v547.toNat - 3 * v554.toNat - 8) :
    let scr' :=
      (((((((scr.set v559.toNat (BitVec.setWidth 32 v554)).set (v559.toNat + 1)
        (BitVec.setWidth 32 v556)).set (v559.toNat + 2)
        (BitVec.setWidth 32 v557)).set (v559.toNat + 3)
        (BitVec.setWidth 32 v558)).set (v559.toNat + 4) 0#32).set
        (v559.toNat + 5) 0#32).set (v559.toNat + 6)
        (BitVec.setWidth 32 v551)).set (v559.toNat + 7)
        (BitVec.setWidth 32 v561)
    scr'.length = c.scratch_cap ∧
      CongCtrlLayout c scr' g_len.toNat v559.toNat v554.toNat v556.toNat v557.toNat v558.toNat
        v551.toNat v561.toNat ∧
      (∀ idx, idx < g_len.toNat → scr'[idx]? = scr0[idx]?) ∧
      CongHtInv maxA F_cur cv scr0 scr' g_len.toNat v551.toNat v561.toNat := by
  have h232 : 2 ^ 31 < 2 ^ 32 := by decide
  exact dense_ctrl_setup_ok hlen hpref (fun t ht => hht_k t (by omega))
    (by rw [hv559]; omega) (by rw [hv559, hv558]; omega) (by rw [hv559]; omega) (by omega)
    (bv32_trunc_eq_ofNat v554 (by omega))
    (bv32_trunc_eq_ofNat v556 (by rw [hv556]; omega))
    (bv32_trunc_eq_ofNat v557 (by rw [hv557]; omega))
    (bv32_trunc_eq_ofNat v558 (by rw [hv558]; omega))
    (bv32_trunc_eq_ofNat v551 (by rw [hv551]; omega))
    (bv32_trunc_eq_ofNat v561 (by omega))
    (by omega) hp20 hv554_p hv554_max hpos561
    (by rw [hv558, hv557]; omega) (by rw [hv557, hv556]; omega)
    (by rw [hv556, hv551]; omega) (by rw [hv551]; omega)

private def FullMemNoScr (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
    array64 (c.hdr + 32) (hdrTailWords c s) ⋆ FullCoreArrays c s.core ⋆
    (FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆ FullScrWksArrs c s.scratch ⋆
      FullScrMetaArrs c s.scratch ⋆
      (array (t := i32) c.pDelayed s.scratch.delayed ⋆
        array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
        array (t := i32) c.pExtendStk s.scratch.extend_stk)) ⋆ c.pad

private theorem fullMem_split_scr {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (FullMem c s ⋆ R) m) :
    (array (t := i32) c.pScratchBuf s.scratch.scratch_buf ⋆ (FullMemNoScr c s ⋆ R)) m := by
  unfold FullMem FullScratchArrays FullScrDynArrs at h
  unfold FullMemNoScr
  have h1 : (((dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
      s.core.d_cur s.core.d_val ⋆ array64 (c.hdr + 32) (hdrTailWords c s) ⋆
      FullCoreArrays c s.core ⋆
      (FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆ FullScrWksArrs c s.scratch ⋆
        FullScrMetaArrs c s.scratch ⋆
        (array (t := i32) c.pDelayed s.scratch.delayed ⋆
          array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
          array (t := i32) c.pExtendStk s.scratch.extend_stk))) ⋆
      array (t := i32) c.pScratchBuf s.scratch.scratch_buf) ⋆ (c.pad ⋆ R)) m := by
    simpa only [sep_assoc] using h
  rw [sep_comm _ (array (t := i32) c.pScratchBuf s.scratch.scratch_buf), sep_assoc] at h1
  simpa only [sep_assoc] using h1

private theorem fullMem_join_scr {c : FullCfg} {s : FullState} {scr' : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (h : (array (t := i32) c.pScratchBuf scr' ⋆ (FullMemNoScr c s ⋆ R)) m) :
    (FullMem c { core := s.core, scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m := by
  let s' : FullState := { core := s.core, scratch := { s.scratch with scratch_buf := scr' } }
  have heq1 : hdrTailWords c s' = hdrTailWords c s := rfl
  have heq2 : FullScrByteArrs c s'.scratch = FullScrByteArrs c s.scratch := rfl
  have heq3 : FullScrU32A c s'.scratch = FullScrU32A c s.scratch := rfl
  have heq4 : FullScrWksArrs c s'.scratch = FullScrWksArrs c s.scratch := rfl
  have heq5 : FullScrMetaArrs c s'.scratch = FullScrMetaArrs c s.scratch := rfl
  change (FullMem c s' ⋆ R) m
  unfold FullMem FullScratchArrays FullScrDynArrs
  rw [heq1, heq2, heq3, heq4, heq5]
  unfold FullMemNoScr at h
  have h1 : (array (t := i32) c.pScratchBuf scr' ⋆
      ((dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
        s.core.d_cur s.core.d_val ⋆ array64 (c.hdr + 32) (hdrTailWords c s) ⋆
        FullCoreArrays c s.core ⋆
        (FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆ FullScrWksArrs c s.scratch ⋆
          FullScrMetaArrs c s.scratch ⋆
          (array (t := i32) c.pDelayed s.scratch.delayed ⋆
            array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
            array (t := i32) c.pExtendStk s.scratch.extend_stk))) ⋆ (c.pad ⋆ R))) m := by
    simpa only [sep_assoc] using h
  rw [← sep_assoc, sep_comm (array (t := i32) c.pScratchBuf scr')] at h1
  simpa only [sep_assoc] using h1

private theorem arr32_store_step {Γ : Env} {Q : Post [i64]} {X : XPost} {base i : BitVec 64}
    {v : BitVec 32} {scr : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    {e : Expr Val Cont [i64]}
    (hm : (array (t := i32) base scr ⋆ R) m) (hi : i.toNat < scr.length)
    (hk : ∀ m', (array (t := i32) base (scr.set i.toNat v) ⋆ R) m' → wp Γ Q X e m') :
    wp Γ Q X (Expr.store (t := i32) (Arg.var v) (Arg.var (base + i * 4)) e) m := by
  c0_hstep
  exact hk _ (by assumption)

private theorem arr32_store0_step {Γ : Env} {Q : Post [i64]} {X : XPost} {base i : BitVec 64}
    {scr : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {e : Expr Val Cont [i64]}
    (hm : (array (t := i32) base scr ⋆ R) m) (hi : i.toNat < scr.length)
    (hk : ∀ m', (array (t := i32) base (scr.set i.toNat 0#32) ⋆ R) m' → wp Γ Q X e m') :
    wp Γ Q X (Expr.store (t := i32) (Arg.imm 0) (Arg.var (base + i * 4)) e) m := by
  c0_hstep
  exact hk _ (by assumption)

/-! ### Main theorem: `full_congruence_dense_wp` -/

theorem full_congruence_dense_wp (Γ : Env)
    (hBin : Γ.Has "full_cong_extract_binaries" Spec.fullCongExtractBinariesSpec)
    (hUnits : Γ.Has "full_cong_find_units_equivs" Spec.fullCongFindUnitsEquivsSpec)
    (hIte : Γ.Has "full_cong_extract_ite_all_m7" Spec.fullCongExtractIteAllM7Spec)
    (hFid : Γ.Has "full_cong_extract_from_fid" Spec.fullCongExtractFromFidSpec)
    (hWkl : Γ.Has "full_cong_worklist" Spec.fullCongWorklistSpec)
    (hFwd : Γ.Has "full_cong_fwd_subsume" Spec.fullCongFwdSubsumeSpec) :
    ∀ a m Q X, Spec.fullCongruenceDenseSpec a m Q X →
      Func.wp Γ full_congruence_dense_body a m Q X := by
  rintro ⟨h, tick_lim, ⟨⟩⟩ m0 Q X ⟨c, F0, s0, R, hh, hd0, hm0, hQ⟩
  subst hh
  have hscr_lt31 : c.scratch_cap < 2 ^ 31 := Nat.lt_trans c.hscr (by decide)
  have hscr_lt64 : c.scratch_cap < 2 ^ 64 := Nat.lt_trans hscr_lt31 (by decide)
  have hmax_lt31 : c.max_vars < 2 ^ 31 := Nat.lt_trans c.hmaxv (by decide)
  have hmax_lt64 : c.max_vars < 2 ^ 64 := Nat.lt_trans hmax_lt31 (by decide)
  have hcv_le_max : s0.core.cur_vars ≤ c.max_vars := hd0.1.lengths.core_ok.cur_vars_le
  have hcv_lt64 : s0.core.cur_vars < 2 ^ 64 := Nat.lt_of_le_of_lt hcv_le_max hmax_lt64
  c0_hsplit
  · c0_hsteps!; exact hQ 1#64 s0 m0 hd0 rfl rfl (Or.inl rfl) (fun h => by cases h) hm0
  c0_hsplit
  · c0_hsteps!; exact hQ 1#64 s0 m0 hd0 rfl rfl (Or.inl rfl) (fun h => by cases h) hm0
  have hscr256 : 256 ≤ c.scratch_cap := by
    have hnot : ¬ c.scratch_cap % 2 ^ 64 < (256#64 : BitVec 64).toNat := by assumption
    rw [Nat.mod_eq_of_lt hscr_lt64, BitVec.toNat_ofNat] at hnot; omega
  rcases hd0.1.witness with ⟨F_cur, hW0⟩
  have hdW0 : FullDenseInvW c F0 F_cur s0 :=
    ⟨hd0.1.lengths, hW0, hd0.2.1, hd0.2.2.1, hd0.2.2.2.1, hd0.2.2.2.2.1, hd0.2.2.2.2.2⟩
  c0_hstraight
  c0_hcall hBin
  refine ⟨c, F0, F_cur, _, R, rfl,
    fullDenseInvW_with_antsz_ressz hdW0 0#64 s0.scratch.res_sz,
    by assumption, fun r1 s1 m1 hd1 hcv1 hfuel1 hr1 huns1 hm1 => ?_⟩
  dsimp only at hcv1 hfuel1
  c0_hsplit
  · have hr1_20 : r1 = 20#64 := hc
    c0_hsteps!
    exact hQ 20#64 _ _ (fullDenseInvW_to_dense
      (fullDenseInvW_with_antsz_ressz hd1 0#64 s1.scratch.res_sz))
      hcv1 hfuel1 (Or.inr rfl) (fun _ => huns1 hr1_20) (by assumption)
  have h2cv_nat : (BitVec.ofNat 64 s1.core.cur_vars <<<
      BitVec.signExtend 64 1#32).toNat = 2 * s1.core.cur_vars := by
    have hcv1_lt : (BitVec.ofNat 64 s1.core.cur_vars).toNat < 2 ^ 63 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
    rw [bv64_sext_one, bv64_shl1_lt (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  c0_hstraight
  refine wp_loop_inv
    (Inv := fun (i, ()) mem' =>
      ∃ si, FullDenseInvW c F0 F_cur si ∧ si.core.cur_vars = s1.core.cur_vars ∧
        si.core.fuel = s1.core.fuel ∧ si.core.repr.length = 2 * c.max_vars ∧
        i.toNat ≤ 2 * s1.core.cur_vars ∧
        (∀ l, l < i.toNat → (si.core.repr[l]?.getD 0#32).toNat = l) ∧
        (FullMem c si ⋆ R) mem')
    (μ := fun (i, ()) _ => 2 * s1.core.cur_vars - i.toNat)
    (fun J19 hJ19 => by
      c0_hsteps!
      exact hJ19 (0#64, ()) m1 ⟨s1, hd1, rfl, rfl, hd1.1.core_ok.repr_len,
        Nat.zero_le _, fun _ hk => absurd hk (Nat.not_lt_zero _), hm1⟩)
    (fun J19 ⟨i, ⟨⟩⟩ mi ⟨si, hdsi, hcvsi, hfsi, hreplen, hi_le, hrep_id, hmi⟩ ih19 => ?_)
  c0_hsplit
  · have hi_lt : i.toNat < 2 * s1.core.cur_vars := by
      have hlt : i.toNat < (BitVec.ofNat 64 s1.core.cur_vars <<<
          BitVec.signExtend 64 1#32).toNat := by assumption
      omega
    have hi_repr : i.toNat < si.core.repr.length := by omega
    have hi1_nat : (i + 1#64).toNat = i.toNat + 1 := bv64_add1_lt (by omega)
    c0_hsteps!
    refine ih19 (i + 1#64, ()) _ (by dsimp only; omega)
      ⟨_, fullDenseInvW_with_repr hdsi
        (repr' := si.core.repr.set i.toNat (BitVec.setWidth 32 i))
        (by rw [List.length_set, hreplen]),
        hcvsi, hfsi, by rw [List.length_set, hreplen], by omega, fun l hl => ?_, by assumption⟩
    dsimp only; by_cases hli : l = i.toNat
    · subst hli
      rw [List.getElem?_set_self hi_repr, Option.getD_some, BitVec.toNat_setWidth,
        Nat.mod_eq_of_lt (by omega)]
    · rw [List.getElem?_set_ne (Ne.symm hli)]; exact hrep_id l (by omega)
  have hcv_si : 2 * si.core.cur_vars ≤ si.core.repr.length := by rw [hcvsi]; omega
  have hrepr_inv : FullCongReprInv F_cur (2 * si.core.cur_vars) si.core.repr :=
    fullCongReprInv_of_id F_cur (2 * si.core.cur_vars) si.core.repr hcv_si
      (fun l hl => hrep_id l (by omega))
  c0_hstraight
  refine wp_loop_inv
    (Inv := fun (k, ()) mem' =>
      ∃ sk, FullDenseInvW c F0 F_cur sk ∧ sk.core = si.core ∧
        k.toNat ≤ si.core.cur_vars ∧ (FullMem c sk ⋆ R) mem')
    (μ := fun (k, ()) _ => si.core.cur_vars - k.toNat)
    (fun J22 hJ22 => by
      c0_hsteps!; exact hJ22 (0#64, ()) mi ⟨si, hdsi, rfl, Nat.zero_le _, hmi⟩)
    (fun J22 ⟨k, ⟨⟩⟩ mk ⟨sk, hdsk, hck, hk_le, hmk⟩ ih22 => ?_)
  c0_hsplit
  · obtain ⟨hk_lt, hk_tm, hk1_nat, hdsk'⟩ :=
      dense_tmk_step (cv := si.core.cur_vars) hdsk (by rw [hck]) (by rw [hcvsi]; exact hc)
        (by rw [hcvsi, hcv1]; exact hcv_le_max)
    c0_hsteps!
    exact ih22 (k + 1#64, ()) _
      (by dsimp only; rw [hk1_nat]; exact Nat.sub_lt_sub_left hk_lt (Nat.lt_succ_self _))
      ⟨_, hdsk', hck, by rw [hk1_nat]; exact hk_lt, by assumption⟩
  have hrepr_sk : FullCongReprInv F_cur (2 * sk.core.cur_vars) sk.core.repr := by
    rw [hck]; exact hrepr_inv
  c0_hstraight
  c0_hcall hUnits
  refine ⟨c, F0, F_cur, sk, R, rfl, hdsk, hrepr_sk, hmk,
    fun r2 s2 m2 hd2 hcv2 hfuel2 hrepr2 hr2 huns2 hm2 => ?_⟩
  c0_hsplit
  · have hr2_20 : r2 = 20#64 := hc
    refine wp_loop_inv
      (Inv := fun (k, ()) mem' =>
        ∃ sk2, FullDenseInvW c F0 F_cur sk2 ∧ sk2.core = s2.core ∧
          k.toNat ≤ s2.core.cur_vars ∧ (FullMem c sk2 ⋆ R) mem')
      (μ := fun (k, ()) _ => s2.core.cur_vars - k.toNat)
      (fun J27 hJ27 => by
        c0_hsteps!; exact hJ27 (0#64, ()) m2 ⟨s2, hd2, rfl, Nat.zero_le _, hm2⟩)
      (fun J27 ⟨k, ⟨⟩⟩ mk2 ⟨sk2, hdsk2, hc2, hk2_le, hmk2⟩ ih27 => ?_)
    c0_hsplit
    · obtain ⟨hk2_lt, hk2_tm, hk2_1, hdsk2'⟩ :=
        dense_tmk_step (cv := s2.core.cur_vars) hdsk2 (by rw [hc2])
          (by rw [hcv2, hck, hcvsi]; exact hc) (by rw [hcv2, hck, hcvsi, hcv1]; exact hcv_le_max)
      c0_hsteps!
      exact ih27 (k + 1#64, ()) _
        (by dsimp only; rw [hk2_1]; exact Nat.sub_lt_sub_left hk2_lt (Nat.lt_succ_self _))
        ⟨_, hdsk2', hc2, by rw [hk2_1]; exact hk2_lt, by assumption⟩
    c0_hsteps!
    exact hQ 20#64 _ _ (fullDenseInvW_to_dense (fullDenseInvW_with_antsz_ressz hdsk2 0#64 0#64))
      (by rw [hc2, hcv2, hck, hcvsi, hcv1]) (by rw [hc2, hfuel2, hck, hfsi, hfuel1])
      (Or.inr rfl) (fun _ => huns2 hr2_20) (by assumption)
  c0_hstraight
  refine wp_join_group
    (fun (v32, ()) mem' =>
      mem' = m2 ∧ 128 ≤ v32.toNat ∧ v32.toNat ≤ c.scratch_cap / 2 ∧ v32.toNat ≤ 16777215)
    (fun J31 ⟨v32, ⟨⟩⟩ m31 ⟨hm31, hv32_ge, hv32_half, hv32_cap⟩ => ?_)
    (fun J31 hJ31 => by
      have h16m' : (16777215#64).toNat = 16777215 := by decide
      c0_hsplit
      · c0_hsteps!
        simp [BitVec.toNat_ushiftRight, Nat.mod_eq_of_lt hscr_lt64,
          Nat.shiftRight_eq_div_pow] at hc
        exact hJ31 (16777215#64, ()) m2
          ⟨rfl, by decide, by rw [h16m']; omega, by decide⟩
      · c0_hsteps!
        simp [BitVec.toNat_ushiftRight, Nat.mod_eq_of_lt hscr_lt64,
          Nat.shiftRight_eq_div_pow] at hc
        refine hJ31 _ m2 ⟨rfl, ?_, ?_, ?_⟩ <;>
          (simp [BitVec.toNat_ushiftRight, Nat.mod_eq_of_lt hscr_lt64,
            Nat.shiftRight_eq_div_pow]; try omega))
  rw [hm31]
  have hv32_scr : v32.toNat ≤ c.scratch_cap := by omega
  have hv32_232 : v32.toNat < 2 ^ 32 := by omega
  have hv35_nat : (BitVec.setWidth 32 (v32 >>> (1 : Nat))).toNat = v32.toNat / 2 := by
    rw [BitVec.toNat_setWidth, bv64_ushiftRight1_toNat]; exact Nat.mod_eq_of_lt (by omega)
  c0_hstraight
  c0_hcall hIte
  refine ⟨64, c, F0, F_cur, s2, R, by decide, by decide, rfl, hd2,
    Nat.zero_le _, by rw [hv35_nat]; omega, CongGateSeqOk.done, hm2,
    fun g_ite s3 m3 hd3 hcore3 _ _ _ _ _ _ _ hgi1 hgi2 _ hseq3 hm3 => ?_⟩
  have hg37_nat : (BitVec.setWidth 64 g_ite).toNat = g_ite.toNat := bv_zext32_toNat g_ite
  have hrepr3 : FullCongReprInv F_cur (2 * s3.core.cur_vars) s3.core.repr := by
    rw [hcore3]; exact hrepr2
  c0_hstraight
  refine wp_join_group
    (fun (g_len, ()) mem' =>
      ∃ s4, FullDenseInvW c F0 F_cur s4 ∧
        s4.core.cur_vars = s2.core.cur_vars ∧ s4.core.fuel = s2.core.fuel ∧
        FullCongReprInv F_cur (2 * s4.core.cur_vars) s4.core.repr ∧
        g_len.toNat ≤ v32.toNat ∧
        CongGateSeqOk congAndArityMax F_cur s4.core.cur_vars s4.scratch.scratch_buf g_len.toNat 0 ∧
        (FullMem c s4 ⋆ R) mem')
    (fun J38 ⟨g_len, ⟨⟩⟩ m38 ⟨s4, hd4, hcv4, hfl4, hrepr4, hgl_le, hseq4, hm4⟩ => ?_)
    (fun J38 hJ38 => by
      c0_hsplit
      · c0_hcall hFid
        refine ⟨c, F0, F_cur, s3, R, rfl, hd3, by rw [hg37_nat]; omega, hv32_scr,
          by rw [hg37_nat, hcore3]; exact hseq3, hm3,
          fun r4 s4 m4 hd4 hcv4 hfl4 hrep4 _ _ hr4_cap hseq4 hm4 => ?_⟩
        c0_hsteps!
        exact hJ38 (r4, ()) m4 ⟨s4, hd4, hcv4.trans (congrArg FullCoreState.cur_vars hcore3),
          hfl4.trans (congrArg FullCoreState.fuel hcore3),
          by rw [hcv4, hrep4, hcore3]; exact hrepr2, hr4_cap, by rw [hcv4]; exact hseq4, hm4⟩
      · have hbad : False := by rw [hg37_nat] at *; rw [hv35_nat] at hgi2; omega
        exact hbad.elim)
  c0_hstraight
  refine wp_join_group
    (fun (_unused, ()) mem' =>
      ∃ s5, FullDenseInvW c F0 F_cur s5 ∧
        s5.core.cur_vars = s2.core.cur_vars ∧ s5.core.fuel = s2.core.fuel ∧
        FullCongReprInv F_cur (2 * s5.core.cur_vars) s5.core.repr ∧ (FullMem c s5 ⋆ R) mem')
    (fun J40 ⟨_unused, ⟨⟩⟩ m40 ⟨s5, hd5, hcv5, hfl5, hrepr5, hm5⟩ => ?_)
    (fun J40 hJ40 => ?_)
  · c0_hstraight
    c0_hcall hFwd
    refine ⟨c, F0, F_cur, s5, R, rfl, hd5, hrepr5, hm5,
      fun r6 s6 m6 hd6 hcv6 hfuel6 hrepr6 hr6 huns6 hm6 => ?_⟩
    c0_hsplit
    · have hr6_20 : r6 = 20#64 := hc
      refine wp_loop_inv
        (Inv := fun (k, ()) mem' =>
          ∃ sk6, FullDenseInvW c F0 F_cur sk6 ∧ sk6.core = s6.core ∧
            k.toNat ≤ s2.core.cur_vars ∧ (FullMem c sk6 ⋆ R) mem')
        (μ := fun (k, ()) _ => s2.core.cur_vars - k.toNat)
        (fun J44 hJ44 => by c0_hsteps!; exact hJ44 (0#64, ()) m6 ⟨s6, hd6, rfl, Nat.zero_le _, hm6⟩)
        (fun J44 ⟨k, ⟨⟩⟩ mk6 ⟨sk6, hdsk6, hc6, hk6_le, hmk6⟩ ih44 => ?_)
      c0_hsplit
      · obtain ⟨hk6_lt, hk6_tm, hk6_1, hdsk6'⟩ :=
          dense_tmk_step (cv := s2.core.cur_vars) hdsk6 (by rw [hc6, hcv6, hcv5])
            (by rw [hcv2, hck, hcvsi]; exact hc)
            (by rw [hcv2, hck, hcvsi, hcv1]; exact hcv_le_max)
        c0_hsteps!
        exact ih44 (k + 1#64, ()) _
          (by dsimp only; rw [hk6_1]; exact Nat.sub_lt_sub_left hk6_lt (Nat.lt_succ_self _))
          ⟨_, hdsk6', hc6, by rw [hk6_1]; exact hk6_lt, by assumption⟩
      c0_hsteps!
      exact hQ 20#64 _ _ (fullDenseInvW_to_dense (fullDenseInvW_with_antsz_ressz hdsk6 0#64 0#64))
        (by rw [hc6, hcv6, hcv5, hcv2, hck, hcvsi, hcv1])
        (by rw [hc6, hfuel6, hfl5, hfuel2, hck, hfsi, hfuel1])
        (Or.inr rfl) (fun _ => huns6 hr6_20) (by assumption)
    refine wp_loop_inv
      (Inv := fun (k, ()) mem' =>
        ∃ sk6, FullDenseInvW c F0 F_cur sk6 ∧ sk6.core = s6.core ∧
          k.toNat ≤ s2.core.cur_vars ∧ (FullMem c sk6 ⋆ R) mem')
      (μ := fun (k, ()) _ => s2.core.cur_vars - k.toNat)
      (fun J44 hJ44 => by c0_hsteps!; exact hJ44 (0#64, ()) m6 ⟨s6, hd6, rfl, Nat.zero_le _, hm6⟩)
      (fun J44 ⟨k, ⟨⟩⟩ mk6 ⟨sk6, hdsk6, hc6, hk6_le, hmk6⟩ ih44 => ?_)
    c0_hsplit
    · obtain ⟨hk6_lt, hk6_tm, hk6_1, hdsk6'⟩ :=
        dense_tmk_step (cv := s2.core.cur_vars) hdsk6 (by rw [hc6, hcv6, hcv5])
          (by rw [hcv2, hck, hcvsi]; exact hc)
          (by rw [hcv2, hck, hcvsi, hcv1]; exact hcv_le_max)
      c0_hsteps!
      exact ih44 (k + 1#64, ()) _
        (by dsimp only; rw [hk6_1]; exact Nat.sub_lt_sub_left hk6_lt (Nat.lt_succ_self _))
        ⟨_, hdsk6', hc6, by rw [hk6_1]; exact hk6_lt, by assumption⟩
    c0_hstraight
    let s_end : FullState :=
      { core := sk6.core, scratch := { sk6.scratch with ant_sz := 0#64, res_sz := 0#64 } }
    have hd_end := fullDenseInvW_with_antsz_ressz hdsk6 0#64 0#64
    refine wp_join_group
      (fun (r_fin, ()) mem' =>
        (r_fin = 20#64 ∨ r_fin = 1#64) ∧ (r_fin = 20#64 → F0.Unsat) ∧
          (FullMem c s_end ⋆ R) mem')
      (fun J49 ⟨r_fin, ⟨⟩⟩ m49 ⟨hr_or, huns_f, hm49⟩ => by
        c0_hsteps!
        exact hQ r_fin s_end m49 (fullDenseInvW_to_dense hd_end)
          (by rw [hc6, hcv6, hcv5, hcv2, hck, hcvsi, hcv1])
          (by rw [hc6, hfuel6, hfl5, hfuel2, hck, hfsi, hfuel1]) hr_or.symm huns_f hm49)
      (fun J49 hJ49 => ?_)
    c0_hsplit
    · have hinc : s6.core.inconsistent ≠ 0#64 := by rw [← hc6]; exact hc
      have huns_fin : F0.Unsat := hd6.2.1.ext_sound.2 (hd6.2.1.inconsistent_sound hinc)
      c0_hsteps!; exact hJ49 (20#64, ()) _ ⟨Or.inl rfl, fun _ => huns_fin, by assumption⟩
    · c0_hsteps!; exact hJ49 (1#64, ()) _ ⟨Or.inr rfl, (fun h => by cases h), by assumption⟩
  c0_hsplit; rotate_left
  · c0_hsteps!; exact hJ40 (k, ()) m38 ⟨s4, hd4, hcv4, hfl4, hrepr4, hm4⟩
  c0_hsplit; rotate_left
  · c0_hsteps!; exact hJ40 (k, ()) m38 ⟨s4, hd4, hcv4, hfl4, hrepr4, hm4⟩
  have hgl_pos : 0 < g_len.toNat := by assumption
  have hgl_le' : g_len.toNat ≤ v32.toNat := by assumption
  have hv545_nat : (BitVec.ofNat 64 c.scratch_cap - g_len).toNat = c.scratch_cap - g_len.toNat := by
    have hcap_mod : (BitVec.ofNat 64 c.scratch_cap).toNat = c.scratch_cap := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hscr_lt64]
    rw [bv64_sub_toNat (hcap_mod.symm ▸ Nat.le_trans hgl_le hv32_scr), hcap_mod]
  c0_hstraight
  refine wp_loop_inv
    (Inv := fun (v547, ()) mem' =>
      mem' = m38 ∧ (∃ p, 6 ≤ p ∧ p ≤ 20 ∧ v547.toNat = 2 ^ p) ∧
        64 ≤ v547.toNat ∧ v547.toNat ≤ 1048576 ∧
        (v547.toNat = 64 ∨ 2 * v547.toNat ≤ c.scratch_cap - g_len.toNat))
    (μ := fun (v547, ()) _ => 1048576 - v547.toNat)
    (fun J546 hJ546 => by
      c0_hsteps!
      exact hJ546 (64#64, ()) m38
        ⟨rfl, ⟨6, by decide, by decide, by decide⟩, by decide, by decide, Or.inl (by decide)⟩)
    (fun J546 ⟨v547, ⟨⟩⟩ m546
      ⟨hm546, ⟨p547, hp547_6, hp547_20, hv547_p⟩, hv547_ge, hv547_le, hv547_top⟩ ih546 => ?_)
  rw [hm546]; c0_hstraight
  refine wp_join_group
    (fun () mem' => mem' = m38 ∧ v547.toNat + 56 ≤ c.scratch_cap - g_len.toNat)
    (fun J548 ⟨⟩ m548 ⟨hm548, hv547_56⟩ => ?_)
    (fun J548 hJ548 => by
      c0_hsplit; rotate_left
      · c0_hsteps!
        exact hJ548 () m38
          ⟨rfl, cong_ht_bkt_bound hscr256 (Nat.le_trans hgl_le hv32_half) hv547_ge hv547_top⟩
      c0_hsplit; rotate_left
      · c0_hsteps!
        exact hJ548 () m38
          ⟨rfl, cong_ht_bkt_bound hscr256 (Nat.le_trans hgl_le hv32_half) hv547_ge hv547_top⟩
      obtain ⟨hdec, hp', hge', hle', htop'⟩ :=
        dense_ht_step hp547_6 hp547_20 hv547_p hv547_ge hv547_le hscr_lt64
          (Nat.le_trans hgl_le hv32_scr) (by assumption) (by assumption)
      c0_hsteps!; exact ih546 (v547 <<< 1#64, ()) m38 hdec ⟨rfl, hp', hge', hle', htop'⟩)
  rw [hm548]
  obtain ⟨hv551_nat, hv552_nat, hv554_init⟩ := dense_hv551_init hscr_lt64 hv547_56
  c0_hstraight
  refine wp_loop_inv
    (Inv := fun (v554, ()) mem' =>
      mem' = m38 ∧ (∃ p, 4 ≤ p ∧ p ≤ 20 ∧ v554.toNat = 2 ^ p) ∧
        16 ≤ v554.toNat ∧ v554.toNat ≤ congOccBktMax ∧
        3 * v554.toNat + 8 ≤ c.scratch_cap - v547.toNat - g_len.toNat)
    (μ := fun (v554, ()) _ => 1048576 - v554.toNat)
    (fun J553 hJ553 => by
      c0_hsteps!
      exact hJ553 (16#64, ()) m38 ⟨rfl, ⟨4, by decide, by decide, by decide⟩, by decide, by decide,
        hv554_init⟩)
    (fun J553 ⟨v554, ⟨⟩⟩ m553
      ⟨hm553, ⟨p, hp4, hp20, hv554_p⟩, hv554_ge, hv554_max, hv554_3⟩ ih553 => ?_)
  rw [hm553]; c0_hstraight
  refine wp_join_group (fun () mem' => mem' = m38)
    (fun J555 ⟨⟩ m555 hm555 => ?_)
    (fun J555 hJ555 => by
      c0_hsplit; rotate_left
      · c0_hsteps!; exact hJ555 () m38 rfl
      c0_hsplit; rotate_left
      · c0_hsteps!; exact hJ555 () m38 rfl
      c0_hsplit; rotate_left
      · c0_hsteps!; exact hJ555 () m38 rfl
      obtain ⟨hdec, hp', hge', hmax', h3'⟩ :=
        dense_occ_step hp4 hp20 hv554_p hv554_ge hv554_max hscr_lt64 hv554_3
          (by assumption) (by assumption)
      c0_hsteps!; exact ih553 (v554 <<< 1#64, ()) m38 hdec ⟨rfl, hp', hge', hmax', h3'⟩)
  rw [hm555]
  let v551 := BitVec.ofNat 64 c.scratch_cap - v547
  let v556 := v551 - v554
  let v557 := v556 - v554
  let v558 := v557 - v554
  let v559 := v558 - (8 : BitVec 64)
  obtain ⟨hv556_eq, hv557_eq, hv558_eq, hv559_eq⟩ := dense_sub_chain hv551_nat hv554_3
  c0_hstraight
  refine wp_loop_inv
    (Inv := fun (v561, ()) mem' =>
      mem' = m38 ∧ 0 < v561.toNat ∧ v561.toNat ≤ v547.toNat ∧ v561.toNat ≤ 1048576)
    (μ := fun (v561, ()) _ => v547.toNat - v561.toNat)
    (fun J560 hJ560 => by
      c0_hsteps!; exact hJ560 (64#64, ()) m38 ⟨rfl, by decide, hv547_ge, by decide⟩)
    (fun J560 ⟨v561, ⟨⟩⟩ m560 ⟨hm560, hpos561, hle561, hmax561⟩ ih560 => ?_)
  rw [hm560]; c0_hstraight
  refine wp_join_group (fun () mem' => mem' = m38)
    (fun J562 ⟨⟩ m562 hm562 => ?_)
    (fun J562 hJ562 => by
      c0_hsplit; rotate_left
      · c0_hsteps!; exact hJ562 () m38 rfl
      c0_hsplit; rotate_left
      · c0_hsteps!; exact hJ562 () m38 rfl
      obtain ⟨hdec, hpos', hle', hmax'⟩ :=
        dense_ht_sz_step hpos561 (by assumption) hle561 hv547_le (by assumption)
      c0_hsteps!; exact ih560 (v561 <<< 1#64, ()) m38 hdec ⟨rfl, hpos', hle', hmax'⟩)
  rw [hm562]; c0_hstraight
  refine wp_loop_inv
    (Inv := fun (k, ()) mem' =>
      ∃ sk, FullDenseInvW c F0 F_cur sk ∧ sk.core = s4.core ∧ k.toNat ≤ v561.toNat ∧
        (∀ idx, idx < g_len.toNat →
          sk.scratch.scratch_buf[idx]? = s4.scratch.scratch_buf[idx]?) ∧
        (∀ t, t < k.toNat → sk.scratch.scratch_buf[v551.toNat + t]? = some 4294967295#32) ∧
        (FullMem c sk ⋆ R) mem')
    (μ := fun (k, ()) _ => v561.toNat - k.toNat)
    (fun J563 hJ563 => by
      c0_hsteps!
      exact hJ563 (0#64, ()) m38 ⟨s4, hd4, rfl, Nat.zero_le _, fun _ _ => rfl,
        fun _ ht => absurd ht (Nat.not_lt_zero _), hm4⟩)
    (fun J563 ⟨k, ⟨⟩⟩ mk3 ⟨sk, hdsk, hck_s4, hk_le, hpref_k, hht_k, hmk3⟩ ih563 => ?_)
  c0_hsplit
  · obtain ⟨hk_idx, hk_len, hk1_nat, hdec_k, hk1_le, hdsk', hpref_k', hht_k'⟩ :=
      dense_ht_clr_step hdsk hscr_lt31 hv551_nat hle561 hv554_3 (by assumption) hpref_k hht_k
    c0_hsteps!
    exact ih563 (k + 1#64, ()) _ hdec_k ⟨_, hdsk', hck_s4, hk1_le, hpref_k', hht_k', by assumption⟩
  have hsz_scr := hdsk.1.scratch_ok.scratch_buf_len
  obtain ⟨⟨hc0, hl1, hl2, hl3, hl4, hl5, hl6, hl7⟩, hc1, hc2, hc3, hc4, hc5, hc6, hc7⟩ :=
    dense_ctrl_addrs hsz_scr hscr_lt31 hv559_eq hv554_3
  c0_hstep; c0_hstep
  have hmk3_sp :
      (array (t := i32) c.pScratchBuf sk.scratch.scratch_buf ⋆
        (FullMemNoScr c
          { core := sk.core, scratch := { sk.scratch with res_sz := 0#64 } } ⋆ R)) m :=
    fullMem_split_scr hm
  clear hm
  c0_hstep; c0_hstep; c0_hstep
  refine arr32_store_step hmk3_sp hc0 fun m hm => ?_
  c0_hstep; c0_hstep; c0_hstep; c0_hstep
  refine arr32_store_step hm (by simp only [List.length_set]; exact hl1) fun m hm => ?_
  c0_hstep; c0_hstep; c0_hstep; c0_hstep
  refine arr32_store_step hm (by simp only [List.length_set]; exact hl2) fun m hm => ?_
  c0_hstep; c0_hstep; c0_hstep; c0_hstep
  refine arr32_store_step hm (by simp only [List.length_set]; exact hl3) fun m hm => ?_
  c0_hstep; c0_hstep; c0_hstep
  refine arr32_store0_step hm (by simp only [List.length_set]; exact hl4) fun m hm => ?_
  c0_hstep; c0_hstep; c0_hstep
  refine arr32_store0_step hm (by simp only [List.length_set]; exact hl5) fun m hm => ?_
  c0_hstep; c0_hstep; c0_hstep; c0_hstep
  refine arr32_store_step hm (by simp only [List.length_set]; exact hl6) fun m hm => ?_
  c0_hstep; c0_hstep; c0_hstep; c0_hstep
  refine arr32_store_step hm (by simp only [List.length_set]; exact hl7) fun m hm => ?_
  have hmk3_jn := fullMem_join_scr hm
  clear hm hmk3_sp
  rw [hc1, hc2, hc3, hc4, hc5, hc6, hc7] at hmk3_jn
  have hsetup := dense_ctrl_bundle (maxA := congAndArityMax) (F_cur := F_cur)
    (cv := s4.core.cur_vars) hsz_scr hscr_lt31 hpref_k hht_k (by assumption) hgl_le hv32_cap
    hp4 hp20 hv554_p hv554_max hv554_3 hpos561 hle561 hmax561 hv551_nat hv556_eq hv557_eq
    hv558_eq hv559_eq
  have hds_c := fullDenseInvW_with_scr
    (fullDenseInvW_with_antsz_ressz hdsk sk.scratch.ant_sz 0#64) hsetup.1
  c0_hcall hWkl
  refine ⟨c, F0, F_cur, _, s4.scratch.scratch_buf, v554.toNat, v556.toNat, v557.toNat,
    v558.toNat, v551.toNat, v561.toNat, R, rfl, hds_c, by rw [hck_s4]; exact hrepr4,
    hgl_pos, hmax561, by rw [hck_s4]; exact hsetup.2.1, by rw [hck_s4]; exact hseq4,
    hsetup.2.2.1, by rw [hck_s4]; exact hsetup.2.2.2, by assumption,
    fun r5 s5 m5 hd5 hcv5 hfl5 hrepr5 hr5 huns5 hm5 => ?_⟩
  c0_hsplit; rotate_left
  · c0_hsteps!
    exact hJ40 (k, ()) m5 ⟨s5, hd5, by rw [hcv5, hck_s4, hcv4],
      by rw [hfl5, hck_s4, hfl4], hrepr5, hm5⟩
  have hr5_20 : r5 = 20#64 := hc
  refine wp_loop_inv
    (Inv := fun (k, ()) mem' =>
      ∃ sk5, FullDenseInvW c F0 F_cur sk5 ∧ sk5.core = s5.core ∧
        k.toNat ≤ s2.core.cur_vars ∧ (FullMem c sk5 ⋆ R) mem')
    (μ := fun (k, ()) _ => s2.core.cur_vars - k.toNat)
    (fun J598 hJ598 => by c0_hsteps!; exact hJ598 (0#64, ()) m5 ⟨s5, hd5, rfl, Nat.zero_le _, hm5⟩)
    (fun J598 ⟨k, ⟨⟩⟩ mk5 ⟨sk5, hdsk5, hc5, hk5_le, hmk5⟩ ih598 => ?_)
  c0_hsplit
  · obtain ⟨hk5_lt, hk5_tm, hk5_1, hdsk5'⟩ :=
      dense_tmk_step (cv := s2.core.cur_vars) hdsk5 (by rw [hc5, hcv5, hck_s4, hcv4])
        (by rw [hcv2, hck, hcvsi]; exact hc) (by rw [hcv2, hck, hcvsi, hcv1]; exact hcv_le_max)
    c0_hsteps!
    exact ih598 (k + 1#64, ()) _
      (by dsimp only; rw [hk5_1]; exact Nat.sub_lt_sub_left hk5_lt (Nat.lt_succ_self _))
      ⟨_, hdsk5', hc5, by rw [hk5_1]; exact hk5_lt, by assumption⟩
  c0_hsteps!
  exact hQ 20#64 _ _ (fullDenseInvW_to_dense (fullDenseInvW_with_antsz_ressz hdsk5 0#64 0#64))
    (by rw [hc5, hcv5, hck_s4, hcv4, hcv2, hck, hcvsi, hcv1])
    (by rw [hc5, hfl5, hck_s4, hfl4, hfuel2, hck, hfsi, hfuel1])
    (Or.inr rfl) (fun _ => huns5 hr5_20) (by assumption)

end

end LeanQbe.T.Examples.Kissat.Proof.Congruence
