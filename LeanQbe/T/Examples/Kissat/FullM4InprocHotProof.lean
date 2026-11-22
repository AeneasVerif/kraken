module

public import LeanQbe.T.Examples.Kissat.FullM4InprocHot
public import LeanQbe.T.Examples.Kissat.FullM4InprocHotProof1
public import LeanQbe.T.Examples.Kissat.FullM4InprocHotProof0

/-!
# Kissat `D-Full` M4 Track A6 Proofs (`FullM4InprocHotProof`)

Proves exact same-spec `Func.wp` contracts for the three inprocessing hot-spot optimizations in
`LeanQbe.T.Examples.Kissat.FullM4InprocHot` against the canonical `FullSpec` specifications:
1. `full_has_ternary_m4_wp` : `Full.fullHasTernarySpec`
2. `full_kitten_init_m4_wp` : `Full.fullKittenInitSpec`
3. `full_wstack_defrag_m4_wp` : `Full.fullWstackDefragSpec`
Plus closed `3`-row `ModuleOk m4InprocHotEnv m4InprocHotModule` and concrete `Mem 64` non-vacuity.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM4InprocHot

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.KittenMemATactics
open Kraken.Bedrock2.Test

local elab "m4_wp_lets" : tactic => do
  try LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, splitJnz := false } 1000
  catch _ => pure ()

local elab "m4_omega" : tactic => Lean.Elab.Tactic.withMainContext do
  let s ← Lean.Elab.Tactic.saveState
  let drop (t : Lean.Expr) : Bool :=
    t.isForall ||
    (t.find? fun e => match e.constName? with
      | some ``LeanQbe.T.wp | some ``DefragMem | some ``List.Perm
      | some ``M4Sorted | some ``M4WsCovers | some ``FullWsortMaxHeap
      | some ``M4MergeInv
      | some ``WatchStackLayout | some ``FullCoreState.LengthsOk
      | some ``FullScratch.LengthsOk | some ``FullState.LengthsOk
      | some ``LeanQbe.T.Cont | some ``LeanQbe.T.Post | some ``LeanQbe.T.XPost => true
      | _ => false).isSome
  try
    Lean.Elab.Tactic.liftMetaTactic1 fun g => do
      let mut g := g
      for d in (← Lean.getLCtx).decls.toArray.reverse do
        let some d := d | continue
        if d.isImplementationDetail || d.isLet then continue
        let t := d.type
        if drop t then
          if ← Lean.Meta.isProp t then
            try g ← g.clear d.fvarId catch _ => pure ()
      return Option.some g
    Lean.Elab.Tactic.evalTactic (← `(tactic| omega))
  catch _ =>
    s.restore
    Lean.Elab.Tactic.evalTactic (← `(tactic| omega))

local macro "m4_wp_jump" : tactic =>
  `(tactic| (
    try simp only [LeanQbe.T.wp_jump, LeanQbe.T.vals_nil, LeanQbe.T.vals_cons]
    try dsimp only [LeanQbe.T.lift2]
    try simp only [LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm]
    try dsimp only [LeanQbe.T.lift2]
    try simp only [LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm]))

/-! ## 4. `full_wstack_defrag_m4_wp` (Same-Spec Optimization of `full_wstack_defrag`) -/

section DefragM4

private theorem m4_min_add_assoc (a w n : Nat) :
    min (min (a + w) n + w) n = min (a + 2 * w) n := by omega

private theorem m4_bv64_add1_toNat {x : BitVec 64} (hx : x.toNat + 1 < 2 ^ 64) :
    (x + (1 : BitVec 64)).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show ((1 : BitVec 64) : BitVec 64).toNat = 1 from rfl]; omega

private theorem m4_zext_shl1 (x : BitVec 32) :
    (x.setWidth 64 <<< (1 : Nat)).toNat = 2 * x.toNat := by
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide)), Nat.shiftLeft_eq]
  have := x.isLt; omega

private theorem m4_bv64_shl1 {w : BitVec 64} (hw : 2 * w.toNat < 2 ^ 64) :
    (w <<< (1 : Nat)).toNat = 2 * w.toNat := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega

private theorem m4_bv64_shr1 (w : BitVec 64) :
    (w >>> (1 : Nat)).toNat = w.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

private theorem m4_bv64_trunc32 {w : BitVec 64} (hw : w.toNat < 2 ^ 32) :
    (w.setWidth 32).toNat = w.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hw]

private theorem m4_bv32_zext64 (x : BitVec 32) :
    (x.setWidth 64).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide))]

private theorem m4_ptr_mul4_add (p a b : BitVec 64) (hab : a.toNat + b.toNat < 2 ^ 64) :
    p + (a + b) * 4 = p + BitVec.ofNat 64 (4 * (a.toNat + b.toNat)) := by
  rw [ptr_mul4_eq, BitVec.toNat_add, Nat.mod_eq_of_lt hab]

private theorem m4_ptr_mul4_sub1 (p a : BitVec 64) (ha : 0 < a.toNat) :
    p + (a - (1 : BitVec 64)) * 4 = p + BitVec.ofNat 64 (4 * (a.toNat - 1)) := by
  rw [ptr_mul4_eq, BitVec.toNat_sub, show ((1 : BitVec 64) : BitVec 64).toNat = 1 from rfl]
  have := a.isLt; congr 2; congr 1; omega

private theorem m4_ptr_mul4_zext_shl1_add1 (p : BitVec 64) (x : BitVec 32) :
    p + ((x.setWidth 64 <<< (1 : Nat)) + (1 : BitVec 64)) * 4 =
      p + BitVec.ofNat 64 (4 * (2 * x.toNat + 1)) := by
  rw [ptr_mul4_eq, BitVec.toNat_add, m4_zext_shl1,
    show ((1 : BitVec 64) : BitVec 64).toNat = 1 from rfl]
  have := x.isLt; congr 2; congr 1; omega

private theorem m4_ptr_mul4_add1 (p a : BitVec 64) (ha : a.toNat + 1 < 2 ^ 64) :
    p + (a + (1 : BitVec 64)) * 4 = p + BitVec.ofNat 64 (4 * (a.toNat + 1)) := by
  rw [ptr_mul4_eq, BitVec.toNat_add, show ((1 : BitVec 64) : BitVec 64).toNat = 1 from rfl,
    Nat.mod_eq_of_lt ha]

local macro "m4_sift_inner"
    key:ident "," ws0:ident "," _lim:ident "," rl0:ident "," n_nat:term "," mv:term ","
    wvec1:ident "," c:ident "," s:ident "," R:ident "," hdone_br:ident ","
    lo_nat:term "," lim_nat:term "," initTac:term : tactic =>
  `(tactic| (
    refine wp_join_group
      (fun (root, ()) mD =>
        $lo_nat ≤ root.toNat ∧ root.toNat < $lim_nat ∧
        ∃ (wsL : List (BitVec 32)),
          wsL.length = 2 * ($mv) ∧
          (∀ p, $lim_nat ≤ p → wsL[p]? = ($ws0)[p]?) ∧
          ($rl0).toNat < 2 * ($s).core.cur_vars ∧
          (∀ i < $n_nat, i ≠ root.toNat → (wsL[i]?.getD 0#32).toNat < 2 * ($s).core.cur_vars) ∧
          (let wsV := wsL.set root.toNat $rl0;
           wsV.Perm $ws0 ∧ (∀ p, $lim_nat ≤ p → wsV[p]? = ($ws0)[p]?) ∧
           FullWsortMaxHeap $wvec1 wsV $lo_nat $lim_nat) ∧
          DefragMem $c $s $wvec1 wsL ($s).core.wstk $R mD)
      ?_ ?_
    · rintro _ ⟨root, ⟨⟩⟩ mD ⟨hlo_r, hr_lim, wsL, hwsL, hsufL, hrl_lt, hbdL,
        ⟨hpermV, hsufV, hmaxV⟩, hmD⟩
      m4_wp_lets
      refine wp_store_sep_at (ptr := ($c).pWsort + BitVec.ofNat 64 (4 * root.toNat))
        (by try simp only [LeanQbe.T.Arg.val_var]; rw [ptr_mul4_eq])
        (dsm_store_ws (i := root.toNat) $rl0 (by rw [hwsL]; omega) hmD) fun mS hmS => ?_
      m4_wp_lets; m4_wp_jump
      exact $hdone_br mS ⟨wsL.set root.toNat $rl0, by rw [List.length_set, hwsL],
        hpermV, hsufV, hmaxV, hmS⟩
    · intro JB hJB
      m4_wp_lets
      refine wp_loop_inv
        (fun (root, ()) mL =>
          $lo_nat ≤ root.toNat ∧ root.toNat < $lim_nat ∧
          ∃ (wsL : List (BitVec 32)),
            wsL.length = 2 * ($mv) ∧
            (∀ p, $lim_nat ≤ p → wsL[p]? = ($ws0)[p]?) ∧
            ($rl0).toNat < 2 * ($s).core.cur_vars ∧
            (∀ i < $n_nat, i ≠ root.toNat → (wsL[i]?.getD 0#32).toNat < 2 * ($s).core.cur_vars) ∧
            (let wsV := wsL.set root.toNat $rl0;
             wsV.Perm $ws0 ∧ (∀ p, $lim_nat ≤ p → wsV[p]? = ($ws0)[p]?) ∧
             M4MaxHeapHole $key wsV $lo_nat $lim_nat root.toNat ∧
             M4HoleParent $key wsV $lo_nat $lim_nat root.toNat) ∧
            DefragMem $c $s $wvec1 wsL ($s).core.wstk $R mL)
        (fun (root, ()) _ => $lim_nat - root.toNat) ?_ ?_
      · exact $initTac
      · rintro JL ⟨root, ⟨⟩⟩ mL ⟨hlo_r, hr_lim, wsL, hwsL, hsufL, hrl_lt, hbdL,
          ⟨hpermV, hsufV, hmaxV, hparV⟩, hmL⟩ hJL
        m4_wp_lets
        simp only [LeanQbe.T.wp_jnz, LeanQbe.T.Arg.val_imm]
        refine ⟨fun _ => ?_, fun hfalse => Bool.noConfusion hfalse⟩
        let wsV := wsL.set root.toNat $rl0
        have hwsV_len : wsV.length = 2 * ($mv) := by rw [List.length_set, hwsL]
        m4_wp_lets
        simp only [LeanQbe.T.wp_jnz, LeanQbe.T.Arg.val_var]
        have hch1 : ((root <<< (1 : Nat)) + (1 : BitVec 64)).toNat = 2 * root.toNat + 1 := by
          rw [BitVec.toNat_add, m4_bv64_shl1 (by omega),
            show ((1 : BitVec 64) : BitVec 64).toNat = 1 from rfl]; omega
        refine ⟨fun hch_ge_c => ?_, fun hch_lt_c => ?_⟩
        · have hch_ge : $lim_nat ≤ 2 * root.toNat + 1 := by
            try unfold BitVec.ule at hch_ge_c
            have := of_decide_eq_true hch_ge_c
            rw [hch1] at this; exact this
          m4_wp_lets; m4_wp_jump
          exact hJB _ _ ⟨hlo_r, hr_lim, wsL, hwsL, hsufL, hrl_lt, hbdL,
            ⟨hpermV, hsufV, m4Wsort_sift_done hmaxV (fun h1 => by omega) (fun h2 => by omega)⟩,
            hmL⟩
        · have hch_lt : 2 * root.toNat + 1 < $lim_nat := by
            try unfold BitVec.ule at hch_lt_c
            have := Nat.not_le.mp (of_decide_eq_false hch_lt_c)
            rw [hch1] at this; exact this
          have hch_ne : 2 * root.toNat + 1 ≠ root.toNat := by omega
          have hcl_lt : 2 * root.toNat + 1 < wsL.length := by rw [hwsL]; omega
          have hcl_cv : (wsL[2 * root.toNat + 1]'hcl_lt).toNat < 2 * ($s).core.cur_vars := by
            have := hbdL (2 * root.toNat + 1) (by omega) hch_ne
            rwa [List.getElem?_eq_getElem hcl_lt, Option.getD_some] at this
          have hcl2_lt : 2 * (wsL[2 * root.toNat + 1]'hcl_lt).toNat < ($wvec1).length := by omega
          m4_wp_lets
          refine wp_load_sep_at (ptr := ($c).pWsort + BitVec.ofNat 64 (4 * (2 * root.toNat + 1)))
            (by try simp only [LeanQbe.T.Arg.val_var]; rw [ptr_mul4_eq, hch1])
            (dsm_load_ws hcl_lt hmL) ?_
          m4_wp_lets
          refine wp_load_sep_at
            (ptr := ($c).pWvec + BitVec.ofNat 64 (4 * (2 * (wsL[2 * root.toNat + 1]'hcl_lt).toNat)))
            (by try simp only [LeanQbe.T.Arg.val_var]; rw [ptr_mul4_eq, m4_zext_shl1])
            (dsm_load_wvec hcl2_lt hmL) ?_
          m4_wp_lets
          refine wp_join_group
            (fun (ch, cl, co, ()) mC =>
              mC = mL ∧ ch.toNat < $lim_nat ∧ (ch.toNat = 2 * root.toNat + 1 ∨
                ch.toNat = 2 * root.toNat + 2) ∧
              wsL[ch.toNat]? = some cl ∧ ($wvec1)[2 * cl.toNat]? = some co ∧
              (2 * root.toNat + 1 < $lim_nat →
                $key (m4WsVal wsV (2 * root.toNat + 1)) ≤ co.toNat) ∧
              (2 * root.toNat + 2 < $lim_nat →
                $key (m4WsVal wsV (2 * root.toNat + 2)) ≤ co.toNat))
            ?_ ?_
          · rintro _ ⟨ch, cl, co, ⟨⟩⟩ mC ⟨hmC_eq, hch_lim, hch_disj, hcl_opt, hco_opt, hs1, hs2⟩
            subst hmC_eq
            have hrc : root.toNat ≠ ch.toNat := by rcases hch_disj with h | h <;> omega
            have hcl_len_ch : ch.toNat < wsL.length := by rw [hwsL]; omega
            have hcl_eq : cl = wsL[ch.toNat]'hcl_len_ch := by
              rw [List.getElem?_eq_getElem hcl_len_ch] at hcl_opt
              exact (Option.some.inj hcl_opt).symm
            have hcl_cv_ch : cl.toNat < 2 * ($s).core.cur_vars := by
              have := hbdL ch.toNat (by omega) hrc.symm
              rwa [hcl_opt, Option.getD_some] at this
            have hco_len_ch : 2 * cl.toNat < ($wvec1).length := by omega
            have hco_eq : co = ($wvec1)[2 * cl.toNat]'hco_len_ch := by
              rw [List.getElem?_eq_getElem hco_len_ch] at hco_opt
              exact (Option.some.inj hco_opt).symm
            have hro_val : m4WvecOff ($wvec1) (m4WsVal wsV root.toNat) =
                (($wvec1)[2 * ($rl0).toNat]'(by omega)).toNat := by
              unfold m4WsVal m4WvecOff
              dsimp only [wsV]
              rw [List.getElem?_set_self (by rw [hwsL]; omega), Option.getD_some,
                List.getElem?_eq_getElem (by omega), Option.getD_some]
            have hco_val : m4WvecOff ($wvec1) (m4WsVal wsV ch.toNat) = co.toNat := by
              unfold m4WsVal m4WvecOff
              dsimp only [wsV]
              rw [List.getElem?_set_ne hrc,
                hcl_opt, Option.getD_some, hco_opt, Option.getD_some]
            m4_wp_lets
            simp only [LeanQbe.T.wp_jnz, LeanQbe.T.Arg.val_var]
            refine ⟨fun hbro => ?_, fun hbro => ?_⟩
            · have hge_co : co.toNat ≤ (($wvec1)[2 * ($rl0).toNat]'(by omega)).toNat := by
                try unfold BitVec.ule at hbro
                exact of_decide_eq_true hbro
              m4_wp_lets; m4_wp_jump
              have hs1' : ∀ h1 : 2 * root.toNat + 1 < $lim_nat,
                  m4WvecOff ($wvec1) (m4WsVal wsV (2 * root.toNat + 1)) ≤ co.toNat := hs1
              have hs2' : ∀ h2 : 2 * root.toNat + 2 < $lim_nat,
                  m4WvecOff ($wvec1) (m4WsVal wsV (2 * root.toNat + 2)) ≤ co.toNat := hs2
              exact hJB _ _ ⟨hlo_r, hr_lim, wsL, hwsL, hsufL, hrl_lt, hbdL,
                ⟨hpermV, hsufV, m4Wsort_sift_done hmaxV
                  (fun h1 => by rw [hro_val]; exact Nat.le_trans (hs1' h1) hge_co)
                  (fun h2 => by rw [hro_val]; exact Nat.le_trans (hs2' h2) hge_co)⟩, hmL⟩
            · have hlt_co : (($wvec1)[2 * ($rl0).toNat]'(by omega)).toNat < co.toNat := by
                try unfold BitVec.ule at hbro
                exact Nat.lt_of_not_le (of_decide_eq_false hbro)
              m4_wp_lets
              refine wp_store_sep_at (ptr := ($c).pWsort + BitVec.ofNat 64 (4 * root.toNat))
                (by try simp only [LeanQbe.T.Arg.val_var]; rw [ptr_mul4_eq])
                (dsm_store_ws (i := root.toNat) cl (by rw [hwsL]; omega) hmL) fun mS hmS => ?_
              m4_wp_lets; m4_wp_jump
              have hs1' : ∀ h1 : 2 * root.toNat + 1 < $lim_nat,
                  m4WvecOff ($wvec1) (m4WsVal wsV (2 * root.toNat + 1)) ≤ co.toNat := hs1
              have hs2' : ∀ h2 : 2 * root.toNat + 2 < $lim_nat,
                  m4WvecOff ($wvec1) (m4WsVal wsV (2 * root.toNat + 2)) ≤ co.toNat := hs2
              have hsib : (2 * root.toNat + 1 < $lim_nat →
                    $key (m4WsVal wsV (2 * root.toNat + 1)) ≤ $key (m4WsVal wsV ch.toNat)) ∧
                  (2 * root.toNat + 2 < $lim_nat →
                    $key (m4WsVal wsV (2 * root.toNat + 2)) ≤ $key (m4WsVal wsV ch.toNat)) :=
                ⟨fun h1 => by
                   change m4WvecOff ($wvec1) _ ≤ m4WvecOff ($wvec1) _
                   rw [hco_val]; exact hs1' h1,
                 fun h2 => by
                   change m4WvecOff ($wvec1) _ ≤ m4WvecOff ($wvec1) _
                   rw [hco_val]; exact hs2' h2⟩
              have ⟨hmax', hpar'⟩ := m4Wsort_sift_step (lo := $lo_nat) (hi := $lim_nat)
                hlo_r hch_lim (by rw [List.length_set, hwsL]; omega) hch_disj hmaxV hparV
                (by
                  change m4WvecOff ($wvec1) _ < m4WvecOff ($wvec1) _
                  rw [hro_val, hco_val]; exact hlt_co) hsib
              have hsw_eq := m4Set_virt_swap_eq (ws := wsL) (root := root.toNat) (ch := ch.toNat)
                (cl := cl) (rl := $rl0) (by rw [hwsL]; omega) (by rw [hwsL]; omega) hrc hcl_eq
              rw [← hsw_eq] at hmax' hpar'
              have hperm' : ((wsL.set root.toNat cl).set ch.toNat $rl0).Perm $ws0 := by
                rw [hsw_eq]
                exact (m4WsSwap_perm (i := root.toNat) (j := ch.toNat)
                  (by rw [List.length_set, hwsL]; omega)
                  (by rw [List.length_set, hwsL]; omega)).trans hpermV
              have hsuf' : ∀ p, $lim_nat ≤ p →
                  ((wsL.set root.toNat cl).set ch.toNat $rl0)[p]? = ($ws0)[p]? := fun p hp => by
                rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
                exact hsufL p hp
              refine hJL _ _ (by dsimp only; omega)
                ⟨by omega, hch_lim, wsL.set root.toNat cl, by rw [List.length_set, hwsL],
                 fun p hp => by rw [List.getElem?_set_ne (by omega)]; exact hsufL p hp,
                 hrl_lt, fun i hi hne => ?_, ⟨hperm', hsuf', hmax', hpar'⟩, hmS⟩
              by_cases hir : i = root.toNat
              · subst hir; rw [List.getElem?_set_self (by rw [hwsL]; omega),
                  Option.getD_some]
                exact hcl_cv_ch
              · rw [List.getElem?_set_ne (Ne.symm hir)]
                exact hbdL i hi hir
          · intro JC hJC
            m4_wp_lets
            simp only [LeanQbe.T.wp_jnz, LeanQbe.T.Arg.val_var]
            refine ⟨fun hc2 => ?_, fun hc2 => ?_⟩
            · have hch2_lt : 2 * root.toNat + 2 < $lim_nat := by
                try unfold BitVec.ult at hc2
                have := of_decide_eq_true hc2
                rw [BitVec.toNat_add, hch1,
                  show ((1 : BitVec 64) : BitVec 64).toNat = 1 from rfl] at this
                omega
              have hch2_eq : ((root <<< (1 : Nat)) + (1 : BitVec 64) + (1 : BitVec 64)).toNat =
                  2 * root.toNat + 2 := by
                rw [BitVec.toNat_add, hch1, show ((1 : BitVec 64) : BitVec 64).toNat = 1 from rfl]
                omega
              have hch2_ne : 2 * root.toNat + 2 ≠ root.toNat := by omega
              have hch2_len : 2 * root.toNat + 2 < wsL.length := by rw [hwsL]; omega
              have hsl_cv : (wsL[2 * root.toNat + 2]'hch2_len).toNat < 2 * ($s).core.cur_vars := by
                have := hbdL (2 * root.toNat + 2) (by omega) hch2_ne
                rwa [List.getElem?_eq_getElem hch2_len, Option.getD_some] at this
              have hsl2_lt : 2 * (wsL[2 * root.toNat + 2]'hch2_len).toNat < ($wvec1).length := by
                omega
              m4_wp_lets
              refine wp_load_sep_at
                (ptr := ($c).pWsort + BitVec.ofNat 64 (4 * (2 * root.toNat + 2)))
                (by try simp only [LeanQbe.T.Arg.val_var]; rw [ptr_mul4_eq, hch2_eq])
                (dsm_load_ws hch2_len hmL) ?_
              m4_wp_lets
              refine wp_load_sep_at
                (ptr := ($c).pWvec + BitVec.ofNat 64
                  (4 * (2 * (wsL[2 * root.toNat + 2]'hch2_len).toNat)))
                (by try simp only [LeanQbe.T.Arg.val_var]; rw [ptr_mul4_eq, m4_zext_shl1])
                (dsm_load_wvec hsl2_lt hmL) ?_
              m4_wp_lets
              refine wp_join_group
                (fun (ch, cl, co, ()) m2 =>
                  m2 = mL ∧ ch.toNat < $lim_nat ∧
                  (ch.toNat = 2 * root.toNat + 1 ∨ ch.toNat = 2 * root.toNat + 2) ∧
                  wsL[ch.toNat]? = some cl ∧ ($wvec1)[2 * cl.toNat]? = some co ∧
                  $key (m4WsVal wsV (2 * root.toNat + 1)) ≤ co.toNat ∧
                  $key (m4WsVal wsV (2 * root.toNat + 2)) ≤ co.toNat)
                ?_ ?_
              · rintro _ ⟨ch, cl, co, ⟨⟩⟩ m2 ⟨hm2_eq, hch_l, hch_d, hcl_e, hco_e, hs1, hs2⟩
                subst hm2_eq
                m4_wp_jump
                exact hJC _ _ ⟨_root_.rfl, hch_l, hch_d, hcl_e, hco_e, fun _ => hs1, fun _ => hs2⟩
              · intro J2 hJ2
                m4_wp_lets
                simp only [LeanQbe.T.wp_jnz, LeanQbe.T.Arg.val_var]
                have hk1 : m4WvecOff ($wvec1) (m4WsVal wsV (2 * root.toNat + 1)) =
                    (($wvec1)[2 * (wsL[2 * root.toNat + 1]'hcl_lt).toNat]'hcl2_lt).toNat := by
                  unfold m4WsVal m4WvecOff
                  dsimp only [wsV]
                  rw [List.getElem?_set_ne (Ne.symm hch_ne),
                    List.getElem?_eq_getElem hcl_lt, Option.getD_some,
                    List.getElem?_eq_getElem hcl2_lt, Option.getD_some]
                have hk2 : m4WvecOff ($wvec1) (m4WsVal wsV (2 * root.toNat + 2)) =
                    (($wvec1)[2 * (wsL[2 * root.toNat + 2]'hch2_len).toNat]'hsl2_lt).toNat := by
                  unfold m4WsVal m4WvecOff
                  dsimp only [wsV]
                  rw [List.getElem?_set_ne (Ne.symm hch2_ne),
                    List.getElem?_eq_getElem hch2_len, Option.getD_some,
                    List.getElem?_eq_getElem hsl2_lt, Option.getD_some]
                refine ⟨fun hgt => ?_, fun hle => ?_⟩
                · have hgt' :
                      (($wvec1)[2 * (wsL[2 * root.toNat + 1]'hcl_lt).toNat]'hcl2_lt).toNat <
                      (($wvec1)[2 * (wsL[2 * root.toNat + 2]'hch2_len).toNat]'hsl2_lt).toNat := by
                    try unfold BitVec.ult at hgt
                    exact of_decide_eq_true hgt
                  m4_wp_lets
                  m4_wp_jump
                  refine hJ2 _ _ ⟨_root_.rfl, by rw [hch2_eq]; exact hch2_lt,
                    Or.inr hch2_eq, ?_, ?_, ?_, ?_⟩
                  · try simp only [LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm]
                    try dsimp only [LeanQbe.T.lift2]
                    rw [hch2_eq, List.getElem?_eq_getElem hch2_len]
                  · try simp only [LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm]
                    try dsimp only [LeanQbe.T.lift2]
                    rw [List.getElem?_eq_getElem hsl2_lt]
                  · change m4WvecOff ($wvec1) _ ≤ _; rw [hk1]; exact Nat.le_of_lt hgt'
                  · change m4WvecOff ($wvec1) _ ≤ _; rw [hk2]; exact le_refl _
                · have hle' :
                      (($wvec1)[2 * (wsL[2 * root.toNat + 2]'hch2_len).toNat]'hsl2_lt).toNat ≤
                      (($wvec1)[2 * (wsL[2 * root.toNat + 1]'hcl_lt).toNat]'hcl2_lt).toNat := by
                    try unfold BitVec.ult at hle
                    exact Nat.not_lt.mp (of_decide_eq_false hle)
                  m4_wp_jump
                  refine hJ2 _ _
                    ⟨_root_.rfl, by rw [hch1]; exact hch_lt, Or.inl hch1, ?_, ?_, ?_, ?_⟩
                  · try simp only [LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm]
                    try dsimp only [LeanQbe.T.lift2]
                    rw [hch1, List.getElem?_eq_getElem hcl_lt]
                  · try simp only [LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm]
                    try dsimp only [LeanQbe.T.lift2]
                    rw [List.getElem?_eq_getElem hcl2_lt]
                  · change m4WvecOff ($wvec1) _ ≤ _; rw [hk1]; exact le_refl _
                  · change m4WvecOff ($wvec1) _ ≤ _; rw [hk2]; exact hle'
            · have hch2_ge : $lim_nat ≤ 2 * root.toNat + 2 := by
                try unfold BitVec.ult at hc2
                have := Nat.not_lt.mp (of_decide_eq_false hc2)
                rw [BitVec.toNat_add, hch1,
                  show ((1 : BitVec 64) : BitVec 64).toNat = 1 from _root_.rfl] at this
                omega
              m4_wp_jump
              refine hJC _ _ ⟨_root_.rfl, by rw [hch1]; exact hch_lt, Or.inl hch1,
                (by try simp only [LeanQbe.T.Arg.val_var]
                    rw [hch1, List.getElem?_eq_getElem hcl_lt]),
                (by try simp only [LeanQbe.T.Arg.val_var]
                    rw [List.getElem?_eq_getElem hcl2_lt]),
                fun _ => by
                  change m4WvecOff ($wvec1) _ ≤ _
                  unfold m4WsVal m4WvecOff
                  dsimp only [wsV]
                  rw [List.getElem?_set_ne (Ne.symm hch_ne),
                    List.getElem?_eq_getElem hcl_lt, Option.getD_some,
                    List.getElem?_eq_getElem hcl2_lt, Option.getD_some]
                  exact le_refl _,
                fun h2 => by omega⟩))

private def m4ExLetI64 (v : Val i64) (e : Expr Val Cont []) : Expr Val Cont [] :=
  match e with | @Expr.let_ _ _ _ [Ty.bits 64] _ k => k (v, ()) | _ => e

private def m4ExLetBool (v : Bool) (e : Expr Val Cont []) : Expr Val Cont [] :=
  match e with | @Expr.let_ _ _ _ [Ty.bool] _ k => k (v, ()) | _ => e

private def m4ExLdI64 (v : Val i64) (e : Expr Val Cont []) : Expr Val Cont [] :=
  match e with | .load (Ty.bits 64) _ k => k v | _ => e

private def m4ExJnz (b : Bool) (e : Expr Val Cont []) : Expr Val Cont [] :=
  match e with | .jnz _ e1 e2 => if b then e1 else e2 | _ => e

private def m4ExGrp0 (c : Cont []) (e : Expr Val Cont []) : Expr Val Cont [] :=
  match e with
  | @Expr.group _ _ _ [[]] bodies _ =>
    match bodies (c, ()) with | .cons f _ => f () | _ => e
  | _ => e

private def m4ExGrp1 (c : Cont [i64]) (x : Val i64) (e : Expr Val Cont []) : Expr Val Cont [] :=
  match e with
  | @Expr.group _ _ _ [[Ty.bits 64]] bodies _ =>
    match bodies (c, ()) with | .cons f _ => f (x, ()) | _ => e
  | _ => e

private def m4ExGrp3 (c : Cont [i64, i64, i64]) (x y z : Val i64) (e : Expr Val Cont []) :
    Expr Val Cont [] :=
  match e with
  | @Expr.group _ _ _ [[Ty.bits 64, Ty.bits 64, Ty.bits 64]] bodies _ =>
    match bodies (c, ()) with | .cons f _ => f (x, y, z, ()) | _ => e
  | _ => e

private def m4ExGrp4 (c : Cont [i64, i64, i32, .bool]) (a b : Val i64) (d : Val i32) (g : Bool)
    (e : Expr Val Cont []) : Expr Val Cont [] :=
  match e with
  | @Expr.group _ _ _ [[Ty.bits 64, Ty.bits 64, Ty.bits 32, Ty.bool]] bodies _ =>
    match bodies (c, ()) with | .cons f _ => f (a, b, d, g, ()) | _ => e
  | _ => e

private def m4ExGrpK0 (J : Cont []) (e : Expr Val Cont []) : Expr Val Cont [] :=
  match e with
  | @Expr.group _ _ _ [[]] _ k => k (J, ())
  | _ => e

private def m4MergeSortExpr (pWvec pWsort n : Val i64) (J7 : Cont []) : Expr Val Cont [] :=
  let dummyLoop : Cont [i64, i64, i32, .bool] := fun _ _ => True
  let dummy0 : Cont [] := fun _ _ => True
  let e0 := full_wstack_defrag_m4_body Val Cont (0#64, ())
  let e1 := m4ExJnz false (m4ExLetBool false (m4ExLdI64 0#64 (m4ExLetI64 0#64 e0)))
  let e2 := m4ExLdI64 pWsort (m4ExLetI64 0#64 (m4ExLdI64 0#64 (m4ExLetI64 0#64
    (m4ExLdI64 pWvec (m4ExLetI64 0#64 (m4ExLetI64 0#64 (m4ExLetI64 1#64
      (m4ExLdI64 0#64 (m4ExLetI64 0#64 e1)))))))))
  let e3 := m4ExJnz false (m4ExLetBool false (m4ExJnz false (m4ExLetBool false
    (m4ExGrp4 dummyLoop n 0#64 0#32 false e2))))
  let e4 := m4ExGrpK0 dummy0 e3
  let e5 := m4ExJnz false (m4ExLetBool false e4)
  let e6 := m4ExJnz true (m4ExLetBool true e5)
  let e7 := m4ExGrpK0 J7 e6
  m4ExJnz true (m4ExLetBool true (m4ExLetI64 0#64 e7))

private def m4MergeOuterExpr (pWvec pWsort n : Val i64) (J7 : Cont []) : Expr Val Cont [] :=
  let dummyJB : Cont [i64] := fun _ _ => True
  m4ExJnz false (m4ExLetBool false
    (m4ExGrp1 dummyJB 0#64 (m4MergeSortExpr pWvec pWsort n J7)))

private def m4MergePairExpr
    (pWvec pWsort n src_off dst_off width lo mid hi : Val i64)
    (JLo : Cont [i64]) : Expr Val Cont [] :=
  let dummy0 : Cont [] := fun _ _ => True
  let dummyJM : Cont [i64, i64, i64] := fun _ _ => True
  let dummy1 : Cont [i64] := fun _ _ => True
  let eOut := m4ExLetI64 0#64 (m4ExLetI64 0#64 (m4ExLetI64 0#64
    (m4MergeOuterExpr pWvec pWsort n dummy0)))
  let eM := m4ExJnz true (m4ExLetBool true
    (m4ExGrp3 dummyJM src_off dst_off width eOut))
  let eLo := m4ExJnz true (m4ExLetBool true
    (m4ExGrp1 JLo lo (m4ExLetI64 0#64 eM)))
  let eMid := m4ExGrp1 dummy1 mid (m4ExLetI64 0#64 eLo)
  m4ExGrp1 dummy1 hi (m4ExLetI64 0#64 eMid)

local macro "m4_let2" c:term "," a:term "," b:term "," k:term : term =>
  `(Expr.let_ (Op.mk $c ($a, $b, ())) $k)

local macro "m4_addr4" base:term "," off:term "," idx:term "," k:term : term =>
  `(m4_let2 (OpCode.add i64), Arg.var $off, Arg.var $idx, fun s =>
    m4_let2 (OpCode.mul i64), Arg.var s.1, Arg.imm (4 : BitVec 64), fun b =>
    m4_let2 (OpCode.add i64), Arg.var $base, Arg.var b.1, fun p => $k p.1)

local macro "m4_load_arr32" base:term "," off:term "," idx:term "," k:term : term =>
  `(m4_addr4 $base, $off, $idx, fun p => Expr.load i32 (Arg.var p) $k)

local macro "m4_load_key" pWvec:term "," v:term "," k:term : term =>
  `(Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var $v, ())) fun z =>
    Expr.let_ (Op.mk (OpCode.sext 32 64) (Arg.imm (1 : BitVec 32), ())) fun o =>
    m4_let2 (OpCode.shl i64), Arg.var z.1, Arg.var o.1, fun sh =>
    m4_let2 (OpCode.mul i64), Arg.var sh.1, Arg.imm (4 : BitVec 64), fun b =>
    m4_let2 (OpCode.add i64), Arg.var $pWvec, Arg.var b.1, fun p =>
    Expr.load i32 (Arg.var p.1) $k)

private def m4MergeRiTailAst
    (pWsort src_off dst_off width lo hi ri_init ki_init : Val i64)
    (JLo : Cont [i64]) : Expr Val Cont [] :=
  @Expr.group Val Cont [] [[i64, i64]] (fun Js_3 => Blocks.cons (fun p_4 =>
    m4_let2 (.cmp .ult i64 .bool rfl), Arg.var p_4.1, Arg.var hi, fun p_5 =>
    .jnz (Arg.var p_5.1)
      (m4_addr4 pWsort, dst_off, p_4.2.1, fun pDst =>
        m4_load_arr32 pWsort, src_off, p_4.1, fun ld =>
        .store (Arg.var ld) (Arg.var pDst)
          (m4_let2 (.add i64), Arg.var p_4.1, Arg.imm (1 : BitVec 64), fun nr =>
           m4_let2 (.add i64), Arg.var p_4.2.1, Arg.imm (1 : BitVec 64), fun nk =>
           .jump Js_3.1 (Arg.var nr.1, Arg.var nk.1, ())))
      (.let_ (Op.mk (.sext 32 64) (Arg.imm 1#32, ())) fun s1 =>
       m4_let2 (.shl i64), Arg.var width, Arg.var s1.1, fun w2 =>
       m4_let2 (.add i64), Arg.var lo, Arg.var w2.1, fun lo2 =>
       .jump JLo (Arg.var lo2.1, ()))) Blocks.nil)
    fun Js_3 => .jump Js_3.1 (Arg.var ri_init, Arg.var ki_init, ())

private def m4MergeTailAst
    (pWsort src_off dst_off width lo mid hi li_init ri_init ki_init : Val i64)
    (JLo : Cont [i64]) : Expr Val Cont [] :=
  @Expr.group Val Cont [] [[i64, i64]] (fun Js_2 => Blocks.cons (fun p_2 =>
    m4_let2 (.cmp .ult i64 .bool rfl), Arg.var p_2.1, Arg.var mid, fun p_3 =>
    .jnz (Arg.var p_3.1)
      (m4_addr4 pWsort, dst_off, p_2.2.1, fun pDst =>
        m4_load_arr32 pWsort, src_off, p_2.1, fun ld =>
        .store (Arg.var ld) (Arg.var pDst)
          (m4_let2 (.add i64), Arg.var p_2.1, Arg.imm (1 : BitVec 64), fun nl =>
           m4_let2 (.add i64), Arg.var p_2.2.1, Arg.imm (1 : BitVec 64), fun nk =>
           .jump Js_2.1 (Arg.var nl.1, Arg.var nk.1, ())))
      (m4MergeRiTailAst pWsort src_off dst_off width lo hi ri_init p_2.2.1 JLo)) Blocks.nil)
    fun Js_2 => .jump Js_2.1 (Arg.var li_init, Arg.var ki_init, ())

private def m4MergePairAst
    (pWvec pWsort src_off dst_off width lo mid hi : Val i64)
    (JLo : Cont [i64]) : Expr Val Cont [] :=
  @Expr.group Val Cont [] [[i64, i64, i64]] (fun Js => Blocks.cons (fun p =>
    @Expr.group Val Cont [] [[]] (fun _Js_1 => Blocks.cons (fun _ =>
      m4MergeTailAst pWsort src_off dst_off width lo mid hi p.1 p.2.1 p.2.2.1 JLo) Blocks.nil)
    fun Js_1 =>
    m4_let2 (.cmp .ult i64 .bool rfl), Arg.var p.1, Arg.var mid, fun p_1 =>
    .jnz (Arg.var p_1.1)
      (m4_let2 (.cmp .ult i64 .bool rfl), Arg.var p.2.1, Arg.var hi, fun p_2 =>
       .jnz (Arg.var p_2.1)
         (m4_load_arr32 pWsort, src_off, p.1, fun ld =>
          m4_load_arr32 pWsort, src_off, p.2.1, fun ld_1 =>
          @Expr.group Val Cont [] [[i64, i64]] (fun _Js_2 => Blocks.cons (fun p_9 =>
            m4_let2 (.add i64), Arg.var p.2.2.1, Arg.imm (1 : BitVec 64), fun nk =>
            .jump Js.1 (Arg.var p_9.1, Arg.var p_9.2.1, Arg.var nk.1, ())) Blocks.nil)
            fun Js_2 =>
            m4_load_key pWvec, ld, fun ld_2 =>
            m4_load_key pWvec, ld_1, fun ld_3 =>
            m4_let2 (.cmp .ule i32 .bool rfl), Arg.var ld_2, Arg.var ld_3, fun p_19 =>
            .jnz (Arg.var p_19.1)
              (m4_addr4 pWsort, dst_off, p.2.2.1, fun pDst =>
               .store (Arg.var ld) (Arg.var pDst)
                 (m4_let2 (.add i64), Arg.var p.1, Arg.imm (1 : BitVec 64), fun nl =>
                  .jump Js_2.1 (Arg.var nl.1, Arg.var p.2.1, ())))
              (m4_addr4 pWsort, dst_off, p.2.2.1, fun pDst =>
               .store (Arg.var ld_1) (Arg.var pDst)
                 (m4_let2 (.add i64), Arg.var p.2.1, Arg.imm (1 : BitVec 64), fun nr =>
                  .jump Js_2.1 (Arg.var p.1, Arg.var nr.1, ()))))
         (.jump Js_1.1 ()))
      (.jump Js_1.1 ())) Blocks.nil)
  fun Js => .jump Js.1 (Arg.var lo, Arg.var mid, Arg.var lo, ())

private theorem m4_merge_pair_ast_eq
    (pWvec pWsort n src_off dst_off width lo mid hi : Val i64)
    (JLo : Cont [i64]) :
    m4MergePairExpr pWvec pWsort n src_off dst_off width lo mid hi JLo =
      m4MergePairAst pWvec pWsort src_off dst_off width lo mid hi JLo := by
  exact rfl

private theorem m4_merge_ri_tail_wp
    {Γ : Env} {Q : Post []} {X : XPost} {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {n src_off dst_off width lo mid hi ri ki : Val i64}
    {m4 : Mem 64} {wvec1 wsD wsM ws1 : List (BitVec 32)} {JLo : Cont [i64]} {ql : Nat}
    (hmx : c.max_vars < 2 * 2 ^ 28)
    (hcv_le : s.core.cur_vars ≤ c.max_vars) (hn_le : n.toNat ≤ 2 * s.core.cur_vars)
    (h2n_le : 2 * n.toNat ≤ 2 * s.core.cur_vars)
    (hso_do : (src_off.toNat = 0 ∧ dst_off.toNat = n.toNat) ∨
      (src_off.toNat = n.toNat ∧ dst_off.toNat = 0))
    (hw16 : 16 ≤ width.toNat) (hwn_lt : width.toNat < n.toNat)
    (hw_ub : width.toNat < 2 * n.toNat + 16)
    (hw2_eq : (width <<< (1 : Nat)).toNat = 2 * width.toNat)
    (hdisj : dst_off.toNat + n.toNat ≤ src_off.toNat ∨
      src_off.toNat + n.toNat ≤ dst_off.toNat)
    (hlo_le : lo.toNat ≤ n.toNat + 2 * width.toNat)
    (hlo_lt : lo.toNat < n.toNat) (hql : lo.toNat = 2 * width.toNat * ql)
    (hmid_eq : mid.toNat = min (lo.toNat + width.toNat) n.toNat)
    (hhi_eq : hi.toNat = min (mid.toNat + width.toNat) n.toNat)
    (hwsM : wsM.length = 2 * c.max_vars) (hwsD : wsD.length = 2 * c.max_vars)
    (hsufD : ∀ p, src_off.toNat ≤ p → p < src_off.toNat + n.toNat → wsD[p]? = wsM[p]?)
    (hpmD : ((wsD.drop dst_off.toNat).take (min lo.toNat n.toNat)).Perm
      ((wsM.drop src_off.toNat).take (min lo.toNat n.toNat)))
    (hbdD : ∀ p, dst_off.toNat ≤ p → p < dst_off.toNat + min lo.toNat n.toNat →
      m4WsVal wsD p < 2 * s.core.cur_vars)
    (hsrtD : ∀ q, 2 * width.toNat * q < min lo.toNat n.toNat →
      M4Sorted (m4WvecOff wvec1) wsD (dst_off.toNat + 2 * width.toNat * q)
        (dst_off.toNat + min (2 * width.toNat * (q + 1)) n.toNat))
    (hsR : M4Sorted (m4WvecOff wvec1) wsD (src_off.toNat + mid.toNat) (src_off.toNat + hi.toNat))
    (hbdD_src : ∀ q, src_off.toNat ≤ q → q < src_off.toNat + n.toNat →
      m4WsVal wsD q < 2 * s.core.cur_vars)
    (hinv1 : M4MergeInv (m4WvecOff wvec1) wsD src_off.toNat dst_off.toNat
      lo.toNat mid.toNat hi.toNat ws1 mid.toNat ri.toNat ki.toNat)
    (hm4 : DefragMem c s wvec1 ws1 s.core.wstk R m4)
    (hJLo : ∀ (ys : Tup Val [i64]) (m' : Mem 64),
      n.toNat + 2 * width.toNat - ys.1.toNat < n.toNat + 2 * width.toNat - lo.toNat →
      (ys.1.toNat ≤ n.toNat + 2 * width.toNat ∧
        (∃ q, ys.1.toNat = 2 * width.toNat * q) ∧
        ∃ wsD' : List (BitVec 32), wsD'.length = 2 * c.max_vars ∧
          (∀ p, src_off.toNat ≤ p → p < src_off.toNat + n.toNat → wsD'[p]? = wsM[p]?) ∧
          ((wsD'.drop dst_off.toNat).take (min ys.1.toNat n.toNat)).Perm
            ((wsM.drop src_off.toNat).take (min ys.1.toNat n.toNat)) ∧
          (∀ p, dst_off.toNat ≤ p → p < dst_off.toNat + min ys.1.toNat n.toNat →
            m4WsVal wsD' p < 2 * s.core.cur_vars) ∧
          (∀ q, 2 * width.toNat * q < min ys.1.toNat n.toNat →
            M4Sorted (m4WvecOff wvec1) wsD' (dst_off.toNat + 2 * width.toNat * q)
              (dst_off.toNat + min (2 * width.toNat * (q + 1)) n.toNat)) ∧
          DefragMem c s wvec1 wsD' s.core.wstk R m') →
        JLo ys m') :
    wp Γ Q X (m4MergeRiTailAst c.pWsort src_off dst_off width lo hi ri ki JLo) m4 := by
  let key := m4WvecOff wvec1
  m4_wp_lets
  refine wp_loop_inv
    (fun (ri1, ki2, ()) m5 =>
      ∃ ws2 : List (BitVec 32),
        M4MergeInv key wsD src_off.toNat dst_off.toNat
          lo.toNat mid.toNat hi.toNat ws2
          mid.toNat ri1.toNat ki2.toNat ∧
        DefragMem c s wvec1 ws2 s.core.wstk R m5)
    (fun (ri1, _, ()) _ => hi.toNat - ri1.toNat)
    (fun JRi hJRi => ?_) ?_
  · m4_wp_jump
    exact hJRi _ _ ⟨ws1, hinv1, hm4⟩
  · rintro JRi ⟨ri1, ki2, ⟨⟩⟩ m5 ⟨ws2, hinv2, hm5⟩ hJRi
    m4_wp_lets
    simp only [LeanQbe.T.wp_jnz, LeanQbe.T.Arg.val_var]
    refine ⟨fun hrih => ?_, fun hrih => ?_⟩
    · have hri_lt : ri1.toNat < hi.toNat := of_decide_eq_true hrih
      have ⟨hlen2, hlo_li2, hli_mid2, hmid_ri2, hri_hi2,
        hki2, hpre2, _, _, _⟩ := hinv2
      have hsrc_lt : src_off.toNat + ri1.toNat < ws2.length := by m4_omega
      have hdst_lt : dst_off.toNat + ki2.toNat < ws2.length := by m4_omega
      have hsrc_eq : ws2[src_off.toNat + ri1.toNat]'hsrc_lt =
          wsD[src_off.toNat + ri1.toNat]'(by m4_omega) := by
        have h1 := hpre2 (src_off.toNat + ri1.toNat) (by rcases hdisj with h | h <;> m4_omega)
        rw [List.getElem?_eq_getElem hsrc_lt, List.getElem?_eq_getElem (by m4_omega)] at h1
        exact Option.some.inj h1
      m4_wp_lets
      refine wp_load_sep_at
        (ptr := c.pWsort + BitVec.ofNat 64 (4 * (src_off.toNat + ri1.toNat)))
        (m4_ptr_mul4_add _ _ _ (by m4_omega)) (dsm_load_ws hsrc_lt hm5) ?_
      m4_wp_lets
      refine wp_store_sep_at
        (ptr := c.pWsort + BitVec.ofNat 64 (4 * (dst_off.toNat + ki2.toNat)))
        (m4_ptr_mul4_add _ _ _ (by m4_omega))
        (dsm_store_ws (ws2[src_off.toNat + ri1.toNat]'hsrc_lt) hdst_lt hm5) fun mS hmS => ?_
      m4_wp_lets
      m4_wp_jump
      have hv2_lt : (ws2[src_off.toNat + ri1.toNat]'hsrc_lt).toNat < 2 ^ 31 := by
        rw [hsrc_eq]
        have h1 := hbdD_src (src_off.toNat + ri1.toNat) (by m4_omega) (by m4_omega)
        unfold m4WsVal at h1
        rw [List.getElem?_eq_getElem (by m4_omega), Option.getD_some] at h1
        exact Nat.lt_trans h1 (by m4_omega)
      have hinv2' := m4MergeInv_step_r
        (v := ws2[src_off.toNat + ri1.toNat]'hsrc_lt)
        hinv2 hri_lt (by m4_omega) (by m4_omega) (by rcases hdisj with h | h <;> m4_omega)
        hsR hsrc_eq hv2_lt (fun _ hq1 hq2 => absurd hq2 (Nat.not_lt.mpr hq1))
      have hrp : (ri1 + (1 : BitVec 64)).toNat = ri1.toNat + 1 :=
        m4_bv64_add1_toNat (by m4_omega)
      have hkp : (ki2 + (1 : BitVec 64)).toNat = ki2.toNat + 1 :=
        m4_bv64_add1_toNat (by m4_omega)
      exact hJRi _ _ (by dsimp only; m4_omega) ⟨_, by rw [hrp, hkp]; exact hinv2', hmS⟩
    · have hri_eq : ri1.toNat = hi.toNat := by
        have := Nat.not_lt.mp (of_decide_eq_false hrih)
        have := hinv2.2.2.2.2.1; m4_omega
      obtain ⟨hlenF, _, hpreF, hbdF, hsrtF, hpmF⟩ :=
        m4MergeInv_finish hinv2 (le_refl _) (by m4_omega)
      have hlo_2w : (lo + (width <<< (1 : Nat))).toNat = lo.toNat + 2 * width.toNat := by
        rw [BitVec.toNat_add, hw2_eq]; m4_omega
      have hmin_next : min (lo.toNat + 2 * width.toNat) n.toNat = hi.toNat := by
        rw [hhi_eq, hmid_eq, m4_min_add_assoc]
      m4_wp_lets
      m4_wp_jump
      refine hJLo _ _ (by dsimp only; rw [hlo_2w]; m4_omega)
        ⟨by rw [hlo_2w]; m4_omega,
         ⟨ql + 1, by rw [hlo_2w, hql, Nat.mul_add, Nat.mul_one]⟩,
         ws2, by rw [hlenF, hwsD], fun p hp1 hp2 => ?_, ?_, fun p hp1 hp2 => ?_,
         fun q hq => ?_, hm5⟩
      · exact (hpreF p (by rcases hdisj with h | h <;> m4_omega)).trans (hsufD p hp1 hp2)
      · rw [hlo_2w, hmin_next]
        have heq_src :
            (wsD.drop (src_off.toNat + lo.toNat)).take (hi.toNat - lo.toNat) =
            (wsM.drop (src_off.toNat + lo.toNat)).take (hi.toNat - lo.toNat) :=
          m4Slice_congr (by m4_omega) (by m4_omega)
            fun p hp1 hp2 => hsufD _ (by m4_omega) (by m4_omega)
        exact m4Merge_perm_glue (wsD := wsD) (lo := lo.toNat) (by m4_omega) (by m4_omega)
              (by rw [hlenF, hwsD]; m4_omega)
          (fun p hp => hpreF p (by rcases hdisj with h | h <;> m4_omega))
          (by simpa [Nat.min_eq_left (Nat.le_of_lt hlo_lt)] using hpmD)
          (heq_src ▸ hpmF)
      · rw [hlo_2w, hmin_next] at hp2
        by_cases hpd : p < dst_off.toNat + lo.toNat
        · unfold m4WsVal; rw [hpreF p (Or.inl hpd)]
          exact hbdD p hp1 (by rw [Nat.min_eq_left (Nat.le_of_lt hlo_lt)]; exact hpd)
        · have hmem : ws2[p]'(by m4_omega) ∈
              (ws2.drop (dst_off.toNat + lo.toNat)).take (hi.toNat - lo.toNat) := by
            have hgm := List.getElem_mem
              (l := (ws2.drop (dst_off.toNat + lo.toNat)).take (hi.toNat - lo.toNat))
              (n := p - (dst_off.toNat + lo.toNat))
              (by rw [List.length_take, List.length_drop, hlenF, hwsD]
                  exact Nat.lt_min.mpr ⟨by m4_omega, by m4_omega⟩)
            simpa [List.getElem_take, List.getElem_drop,
              show dst_off.toNat + lo.toNat + (p - (dst_off.toNat + lo.toNat)) = p by
                m4_omega] using hgm
          obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp (hpmF.mem_iff.mp hmem)
          simp only [List.length_take, List.length_drop, hwsD] at hj
          rw [List.getElem_take, List.getElem_drop] at hget
          unfold m4WsVal
          rw [List.getElem?_eq_getElem (by m4_omega), Option.getD_some, ← hget]
          have hsrc := hbdD_src (src_off.toNat + lo.toNat + j) (by m4_omega) (by m4_omega)
          unfold m4WsVal at hsrc
          rwa [List.getElem?_eq_getElem (by m4_omega), Option.getD_some] at hsrc
      · rw [hlo_2w, hmin_next] at hq
        by_cases hqq : q = ql
        · subst hqq
          rw [Nat.mul_add, Nat.mul_one, ← hql, hmin_next]
          exact hsrtF
        · have hq_lt_ql : q < ql := by
            rcases Nat.lt_or_gt_of_ne hqq with h | h
            · exact h
            · have hbd := Nat.mul_le_mul_left (2 * width.toNat) (show ql + 1 ≤ q by m4_omega)
              rw [Nat.mul_add, Nat.mul_one, ← hql] at hbd; m4_omega
          have hq_end : 2 * width.toNat * (q + 1) ≤ lo.toNat := by
            have hbd := Nat.mul_le_mul_left (2 * width.toNat) (show q + 1 ≤ ql by m4_omega)
            rwa [Nat.mul_add, Nat.mul_one, ← hql] at hbd
          have hq_end' : 2 * width.toNat * q + 2 * width.toNat ≤ lo.toNat := by
            simpa only [Nat.mul_add, Nat.mul_one] using hq_end
          have hq_lt : 2 * width.toNat * q < min lo.toNat n.toNat :=
            Nat.lt_min.mpr ⟨by m4_omega, by m4_omega⟩
          have hs_q := hsrtD q hq_lt
          intro i j hi1 hij hj1; unfold m4WsVal
          have hj_lt : j < dst_off.toNat + 2 * width.toNat * (q + 1) := by m4_omega
          rw [hpreF i (Or.inl (by m4_omega)), hpreF j (Or.inl (by m4_omega))]
          exact hs_q i j hi1 hij hj1

private theorem m4_merge_tail_wp
    {Γ : Env} {Q : Post []} {X : XPost} {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {n src_off dst_off width lo mid hi li ri ki : Val i64}
    {m3' : Mem 64} {wvec1 wsD wsM wsL' : List (BitVec 32)} {JLo : Cont [i64]} {ql : Nat}
    (hmx : c.max_vars < 2 * 2 ^ 28)
    (hcv_le : s.core.cur_vars ≤ c.max_vars) (hn_le : n.toNat ≤ 2 * s.core.cur_vars)
    (h2n_le : 2 * n.toNat ≤ 2 * s.core.cur_vars)
    (hso_do : (src_off.toNat = 0 ∧ dst_off.toNat = n.toNat) ∨
      (src_off.toNat = n.toNat ∧ dst_off.toNat = 0))
    (hw16 : 16 ≤ width.toNat) (hwn_lt : width.toNat < n.toNat)
    (hw_ub : width.toNat < 2 * n.toNat + 16)
    (hw2_eq : (width <<< (1 : Nat)).toNat = 2 * width.toNat)
    (hdisj : dst_off.toNat + n.toNat ≤ src_off.toNat ∨
      src_off.toNat + n.toNat ≤ dst_off.toNat)
    (hlo_le : lo.toNat ≤ n.toNat + 2 * width.toNat)
    (hlo_lt : lo.toNat < n.toNat) (hql : lo.toNat = 2 * width.toNat * ql)
    (hmid_eq : mid.toNat = min (lo.toNat + width.toNat) n.toNat)
    (hhi_eq : hi.toNat = min (mid.toNat + width.toNat) n.toNat)
    (hwsM : wsM.length = 2 * c.max_vars) (hwsD : wsD.length = 2 * c.max_vars)
    (hsufD : ∀ p, src_off.toNat ≤ p → p < src_off.toNat + n.toNat → wsD[p]? = wsM[p]?)
    (hpmD : ((wsD.drop dst_off.toNat).take (min lo.toNat n.toNat)).Perm
      ((wsM.drop src_off.toNat).take (min lo.toNat n.toNat)))
    (hbdD : ∀ p, dst_off.toNat ≤ p → p < dst_off.toNat + min lo.toNat n.toNat →
      m4WsVal wsD p < 2 * s.core.cur_vars)
    (hsrtD : ∀ q, 2 * width.toNat * q < min lo.toNat n.toNat →
      M4Sorted (m4WvecOff wvec1) wsD (dst_off.toNat + 2 * width.toNat * q)
        (dst_off.toNat + min (2 * width.toNat * (q + 1)) n.toNat))
    (hsL : M4Sorted (m4WvecOff wvec1) wsD (src_off.toNat + lo.toNat) (src_off.toNat + mid.toNat))
    (hsR : M4Sorted (m4WvecOff wvec1) wsD (src_off.toNat + mid.toNat) (src_off.toNat + hi.toNat))
    (hbdD_src : ∀ q, src_off.toNat ≤ q → q < src_off.toNat + n.toNat →
      m4WsVal wsD q < 2 * s.core.cur_vars)
    (hdone_lr : mid.toNat ≤ li.toNat ∨ hi.toNat ≤ ri.toNat)
    (hinvL' : M4MergeInv (m4WvecOff wvec1) wsD src_off.toNat dst_off.toNat
      lo.toNat mid.toNat hi.toNat wsL' li.toNat ri.toNat ki.toNat)
    (hmL' : DefragMem c s wvec1 wsL' s.core.wstk R m3')
    (hJLo : ∀ (ys : Tup Val [i64]) (m' : Mem 64),
      n.toNat + 2 * width.toNat - ys.1.toNat < n.toNat + 2 * width.toNat - lo.toNat →
      (ys.1.toNat ≤ n.toNat + 2 * width.toNat ∧
        (∃ q, ys.1.toNat = 2 * width.toNat * q) ∧
        ∃ wsD' : List (BitVec 32), wsD'.length = 2 * c.max_vars ∧
          (∀ p, src_off.toNat ≤ p → p < src_off.toNat + n.toNat → wsD'[p]? = wsM[p]?) ∧
          ((wsD'.drop dst_off.toNat).take (min ys.1.toNat n.toNat)).Perm
            ((wsM.drop src_off.toNat).take (min ys.1.toNat n.toNat)) ∧
          (∀ p, dst_off.toNat ≤ p → p < dst_off.toNat + min ys.1.toNat n.toNat →
            m4WsVal wsD' p < 2 * s.core.cur_vars) ∧
          (∀ q, 2 * width.toNat * q < min ys.1.toNat n.toNat →
            M4Sorted (m4WvecOff wvec1) wsD' (dst_off.toNat + 2 * width.toNat * q)
              (dst_off.toNat + min (2 * width.toNat * (q + 1)) n.toNat)) ∧
          DefragMem c s wvec1 wsD' s.core.wstk R m') →
        JLo ys m') :
    wp Γ Q X (m4MergeTailAst c.pWsort src_off dst_off width lo mid hi li ri ki JLo) m3' := by
  let key := m4WvecOff wvec1
  m4_wp_lets
  refine wp_loop_inv
    (fun (li1, ki1, ()) m4 =>
      ∃ ws1 : List (BitVec 32),
        M4MergeInv key wsD src_off.toNat dst_off.toNat
          lo.toNat mid.toNat hi.toNat ws1 li1.toNat ri.toNat ki1.toNat ∧
        (mid.toNat ≤ li1.toNat ∨ hi.toNat ≤ ri.toNat) ∧
        DefragMem c s wvec1 ws1 s.core.wstk R m4)
    (fun (li1, _, ()) _ => mid.toNat - li1.toNat)
    (fun JLi hJLi => ?_) ?_
  · exact hJLi _ _ ⟨wsL', hinvL', hdone_lr, hmL'⟩
  · rintro JLi ⟨li1, ki1, ⟨⟩⟩ m4 ⟨ws1, hinv1, hdisj1, hm4⟩ hJLi
    m4_wp_lets
    simp only [LeanQbe.T.wp_jnz, LeanQbe.T.Arg.val_var]
    refine ⟨fun hlim => ?_, fun hlim => ?_⟩
    · have hli_lt : li1.toNat < mid.toNat := of_decide_eq_true hlim
      have hri_eq : ri.toNat = hi.toNat := by have := hinv1.2.2.2.2.1; m4_omega
      have hsrc_lt : src_off.toNat + li1.toNat < ws1.length := by have := hinv1.1; m4_omega
      have hdst_lt : dst_off.toNat + ki1.toNat < ws1.length := by
        have := hinv1.1; have := hinv1.2.2.2.2.2.1; m4_omega
      have hsrc_eq : ws1[src_off.toNat + li1.toNat]'hsrc_lt =
          wsD[src_off.toNat + li1.toNat]'(by m4_omega) := by
        have h1 := hinv1.2.2.2.2.2.2.1 (src_off.toNat + li1.toNat)
          (by rcases hdisj with h | h <;> m4_omega)
        rw [List.getElem?_eq_getElem hsrc_lt, List.getElem?_eq_getElem (by m4_omega)] at h1
        exact Option.some.inj h1
      m4_wp_lets
      refine wp_load_sep_at
        (ptr := c.pWsort + BitVec.ofNat 64 (4 * (src_off.toNat + li1.toNat)))
        (m4_ptr_mul4_add _ _ _ (by m4_omega)) (dsm_load_ws hsrc_lt hm4) ?_
      m4_wp_lets
      refine wp_store_sep_at
        (ptr := c.pWsort + BitVec.ofNat 64 (4 * (dst_off.toNat + ki1.toNat)))
        (m4_ptr_mul4_add _ _ _ (by have := hinv1.2.2.2.2.2.1; m4_omega))
        (dsm_store_ws (ws1[src_off.toNat + li1.toNat]'hsrc_lt) hdst_lt hm4) fun mS hmS => ?_
      m4_wp_lets; m4_wp_jump
      have hv1_lt : (ws1[src_off.toNat + li1.toNat]'hsrc_lt).toNat < 2 ^ 31 := by
        rw [hsrc_eq]
        have h1 := hbdD_src (src_off.toNat + li1.toNat) (by m4_omega) (by m4_omega)
        unfold m4WsVal at h1
        rw [List.getElem?_eq_getElem (by m4_omega), Option.getD_some] at h1
        exact Nat.lt_trans h1 (by m4_omega)
      have hinv1' := m4MergeInv_step_l
        (v := ws1[src_off.toNat + li1.toNat]'hsrc_lt)
        hinv1 hli_lt (by m4_omega) (by have := hinv1.1; m4_omega)
        (by rcases hdisj with h | h <;> m4_omega) hsL hsrc_eq hv1_lt
        (fun _ hq1 hq2 => absurd hq2 (Nat.not_lt.mpr (hri_eq ▸ hq1)))
      have hlp : (li1 + (1 : BitVec 64)).toNat = li1.toNat + 1 :=
        m4_bv64_add1_toNat (by m4_omega)
      have hkp : (ki1 + (1 : BitVec 64)).toNat = ki1.toNat + 1 :=
        m4_bv64_add1_toNat (by have := hinv1.2.2.2.2.2.1; m4_omega)
      exact hJLi _ _ (by dsimp only; m4_omega)
        ⟨_, by rw [hlp, hkp]; exact hinv1', Or.inr (by m4_omega), hmS⟩
    · have hli_eq : li1.toNat = mid.toNat := by
        have := Nat.not_lt.mp (of_decide_eq_false hlim)
        have := hinv1.2.2.1; m4_omega
      exact m4_merge_ri_tail_wp hmx hcv_le hn_le h2n_le hso_do hw16 hwn_lt hw_ub hw2_eq hdisj
        hlo_le hlo_lt hql hmid_eq hhi_eq hwsM hwsD hsufD hpmD hbdD hsrtD hsR hbdD_src
        (by rw [hli_eq] at hinv1; exact hinv1) hm4 hJLo

private theorem m4_merge_pair_wp
    {Γ : Env} {Q : Post []} {X : XPost} {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {n src_off dst_off width lo mid hi : Val i64}
    {mD : Mem 64} {wvec1 wsD wsM : List (BitVec 32)} {JLo : Cont [i64]} {ql : Nat}
    (hmx : c.max_vars < 2 * 2 ^ 28) (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (hn_le : n.toNat ≤ 2 * s.core.cur_vars)
    (h2n_le : 2 * n.toNat ≤ 2 * s.core.cur_vars)
    (hso_do : (src_off.toNat = 0 ∧ dst_off.toNat = n.toNat) ∨
      (src_off.toNat = n.toNat ∧ dst_off.toNat = 0))
    (hw16 : 16 ≤ width.toNat) (hwn_lt : width.toNat < n.toNat)
    (hw_ub : width.toNat < 2 * n.toNat + 16)
    (hw2_eq : (width <<< (1 : Nat)).toNat = 2 * width.toNat)
    (hdisj : dst_off.toNat + n.toNat ≤ src_off.toNat ∨
      src_off.toNat + n.toNat ≤ dst_off.toNat)
    (hwv1 : wvec1.length = 4 * c.max_vars)
    (hwvec_lt : 2 * (2 * s.core.cur_vars) ≤ wvec1.length)
    (hlo_le : lo.toNat ≤ n.toNat + 2 * width.toNat)
    (hlo_lt : lo.toNat < n.toNat) (hql : lo.toNat = 2 * width.toNat * ql)
    (hmid_eq : mid.toNat = min (lo.toNat + width.toNat) n.toNat)
    (hhi_eq : hi.toNat = min (mid.toNat + width.toNat) n.toNat)
    (hwsM : wsM.length = 2 * c.max_vars) (hwsD : wsD.length = 2 * c.max_vars)
    (hsufD : ∀ p, src_off.toNat ≤ p → p < src_off.toNat + n.toNat → wsD[p]? = wsM[p]?)
    (hpmD : ((wsD.drop dst_off.toNat).take (min lo.toNat n.toNat)).Perm
      ((wsM.drop src_off.toNat).take (min lo.toNat n.toNat)))
    (hbdD : ∀ p, dst_off.toNat ≤ p → p < dst_off.toNat + min lo.toNat n.toNat →
      m4WsVal wsD p < 2 * s.core.cur_vars)
    (hsrtD : ∀ q, 2 * width.toNat * q < min lo.toNat n.toNat →
      M4Sorted (m4WvecOff wvec1) wsD (dst_off.toNat + 2 * width.toNat * q)
        (dst_off.toNat + min (2 * width.toNat * (q + 1)) n.toNat))
    (hsL : M4Sorted (m4WvecOff wvec1) wsD (src_off.toNat + lo.toNat) (src_off.toNat + mid.toNat))
    (hsR : M4Sorted (m4WvecOff wvec1) wsD (src_off.toNat + mid.toNat) (src_off.toNat + hi.toNat))
    (hbdD_src : ∀ q, src_off.toNat ≤ q → q < src_off.toNat + n.toNat →
      m4WsVal wsD q < 2 * s.core.cur_vars)
    (hmD : DefragMem c s wvec1 wsD s.core.wstk R mD)
    (hJLo : ∀ (ys : Tup Val [i64]) (m' : Mem 64),
      n.toNat + 2 * width.toNat - ys.1.toNat < n.toNat + 2 * width.toNat - lo.toNat →
      (ys.1.toNat ≤ n.toNat + 2 * width.toNat ∧
        (∃ q, ys.1.toNat = 2 * width.toNat * q) ∧
        ∃ wsD' : List (BitVec 32), wsD'.length = 2 * c.max_vars ∧
          (∀ p, src_off.toNat ≤ p → p < src_off.toNat + n.toNat → wsD'[p]? = wsM[p]?) ∧
          ((wsD'.drop dst_off.toNat).take (min ys.1.toNat n.toNat)).Perm
            ((wsM.drop src_off.toNat).take (min ys.1.toNat n.toNat)) ∧
          (∀ p, dst_off.toNat ≤ p → p < dst_off.toNat + min ys.1.toNat n.toNat →
            m4WsVal wsD' p < 2 * s.core.cur_vars) ∧
          (∀ q, 2 * width.toNat * q < min ys.1.toNat n.toNat →
            M4Sorted (m4WvecOff wvec1) wsD' (dst_off.toNat + 2 * width.toNat * q)
              (dst_off.toNat + min (2 * width.toNat * (q + 1)) n.toNat)) ∧
          DefragMem c s wvec1 wsD' s.core.wstk R m') →
        JLo ys m') :
    wp Γ Q X (m4MergePairAst c.pWvec c.pWsort src_off dst_off width lo mid hi JLo) mD := by
  let key := m4WvecOff wvec1
  m4_wp_lets
  refine wp_loop_inv
    (fun (li, ri, ki, ()) m3 =>
      ∃ wsL : List (BitVec 32),
        M4MergeInv key wsD src_off.toNat dst_off.toNat
          lo.toNat mid.toNat hi.toNat wsL
          li.toNat ri.toNat ki.toNat ∧
        DefragMem c s wvec1 wsL s.core.wstk R m3)
    (fun (li, ri, _, ()) _ => (mid.toNat - li.toNat) +
      (hi.toNat - ri.toNat))
    ?_ ?_
  · intro JM2 hJM2
    m4_wp_lets; m4_wp_jump
    refine hJM2 _ _ ⟨wsD, m4MergeInv_init rfl (by m4_omega) (by m4_omega)
      (fun _ _ => rfl), hmD⟩
  · rintro JM2 ⟨li, ri, ki, ⟨⟩⟩ m3 ⟨wsL, hinvL, hmL⟩ hJM2
    m4_wp_lets
    refine wp_join_group
      (fun _ m3' =>
        (mid.toNat ≤ li.toNat ∨ hi.toNat ≤ ri.toNat) ∧
        ∃ wsL' : List (BitVec 32),
          M4MergeInv key wsD src_off.toNat dst_off.toNat
            lo.toNat mid.toNat hi.toNat wsL'
            li.toNat ri.toNat ki.toNat ∧
          DefragMem c s wvec1 wsL' s.core.wstk R m3')
      ?_ ?_
    · rintro _ ⟨⟩ m3' ⟨hdone_lr, wsL', hinvL', hmL'⟩
      exact m4_merge_tail_wp hmx hcv_le hn_le h2n_le hso_do hw16 hwn_lt hw_ub hw2_eq hdisj
        hlo_le hlo_lt hql hmid_eq hhi_eq hwsM hwsD hsufD hpmD hbdD hsrtD hsL hsR hbdD_src
        hdone_lr hinvL' hmL' hJLo
    · intro JExit hJExit
      m4_wp_lets; simp only [LeanQbe.T.wp_jnz, LeanQbe.T.Arg.val_var]
      refine ⟨fun hlim => ?_, fun hlim => ?_⟩
      · have hli_lt : li.toNat < mid.toNat := of_decide_eq_true hlim
        m4_wp_lets; simp only [LeanQbe.T.wp_jnz, LeanQbe.T.Arg.val_var]
        refine ⟨fun hrih => ?_, fun hrih => ?_⟩
        · have hri_lt : ri.toNat < hi.toNat := of_decide_eq_true hrih
          have hsL_lt : src_off.toNat + li.toNat < wsL.length := by
            have := hinvL.1; m4_omega
          have hsR_lt : src_off.toNat + ri.toNat < wsL.length := by
            have := hinvL.1; m4_omega
          have hll_eq : wsL[src_off.toNat + li.toNat]'hsL_lt =
              wsD[src_off.toNat + li.toNat]'(by m4_omega) := by
            have h1 := hinvL.2.2.2.2.2.2.1 (src_off.toNat + li.toNat)
              (by rcases hdisj with h | h <;> m4_omega)
            rw [List.getElem?_eq_getElem hsL_lt,
              List.getElem?_eq_getElem (by m4_omega)] at h1
            exact Option.some.inj h1
          have hrl_eq : wsL[src_off.toNat + ri.toNat]'hsR_lt =
              wsD[src_off.toNat + ri.toNat]'(by m4_omega) := by
            have h1 := hinvL.2.2.2.2.2.2.1 (src_off.toNat + ri.toNat)
              (by rcases hdisj with h | h <;> m4_omega)
            rw [List.getElem?_eq_getElem hsR_lt,
              List.getElem?_eq_getElem (by m4_omega)] at h1
            exact Option.some.inj h1
          have hll_cv : (wsL[src_off.toNat + li.toNat]'hsL_lt).toNat <
              2 * s.core.cur_vars := by
            rw [hll_eq]
            have h1 := hbdD_src (src_off.toNat + li.toNat) (by m4_omega) (by m4_omega)
            unfold m4WsVal at h1
            rwa [List.getElem?_eq_getElem (by m4_omega), Option.getD_some] at h1
          have hrl_cv : (wsL[src_off.toNat + ri.toNat]'hsR_lt).toNat <
              2 * s.core.cur_vars := by
            rw [hrl_eq]
            have h1 := hbdD_src (src_off.toNat + ri.toNat) (by m4_omega) (by m4_omega)
            unfold m4WsVal at h1
            rwa [List.getElem?_eq_getElem (by m4_omega), Option.getD_some] at h1
          have hll2 : 2 * (wsL[src_off.toNat + li.toNat]'hsL_lt).toNat <
              wvec1.length := by m4_omega
          have hrl2 : 2 * (wsL[src_off.toNat + ri.toNat]'hsR_lt).toNat <
              wvec1.length := by m4_omega
          have hdst_k : dst_off.toNat + ki.toNat < wsL.length := by
            have := hinvL.1; have := hinvL.2.2.2.2.2.1; m4_omega
          m4_wp_lets
          refine wp_load_sep_at
            (ptr := c.pWsort + BitVec.ofNat 64
              (4 * (src_off.toNat + li.toNat)))
            (m4_ptr_mul4_add _ _ _ (by m4_omega))
            (dsm_load_ws hsL_lt hmL) ?_
          m4_wp_lets
          refine wp_load_sep_at
            (ptr := c.pWsort + BitVec.ofNat 64
              (4 * (src_off.toNat + ri.toNat)))
            (m4_ptr_mul4_add _ _ _ (by m4_omega))
            (dsm_load_ws hsR_lt hmL) ?_
          m4_wp_lets
          refine wp_join_group
            (fun (li', ri', ()) m4 =>
              ∃ wsL' : List (BitVec 32),
                M4MergeInv key wsD src_off.toNat dst_off.toNat
                  lo.toNat mid.toNat hi.toNat wsL'
                  li'.toNat ri'.toNat (ki.toNat + 1) ∧
                DefragMem c s wvec1 wsL' s.core.wstk R m4)
            ?_ ?_
          · rintro _ ⟨li', ri', ⟨⟩⟩ m4 ⟨wsL', hinvL', hm4⟩
            m4_wp_lets
            m4_wp_jump
            have hkp : (ki + (1 : BitVec 64)).toNat = ki.toNat + 1 := by
              rw [BitVec.toNat_add,
                show ((1 : BitVec 64) : BitVec 64).toNat = 1 from rfl]
              have := hinvL.2.2.2.2.2.1; m4_omega
            have hdec : (mid.toNat - li'.toNat) + (hi.toNat - ri'.toNat) <
                (mid.toNat - li.toNat) + (hi.toNat - ri.toNat) := by
              have := hinvL'.2.1; have := hinvL'.2.2.1; have := hinvL'.2.2.2.1
              have := hinvL'.2.2.2.2.1; have := hinvL'.2.2.2.2.2.1
              have := hinvL.2.1; have := hinvL.2.2.1; have := hinvL.2.2.2.1
              have := hinvL.2.2.2.2.1; have := hinvL.2.2.2.2.2.1
              m4_omega
            refine hJM2 _ _ hdec ⟨wsL', ?_, hm4⟩
            rwa [hkp]
          · intro JStep hJStep
            m4_wp_lets
            refine wp_load_sep_at
              (ptr := c.pWvec + BitVec.ofNat 64
                (4 * (2 * (wsL[src_off.toNat + li.toNat]'hsL_lt).toNat)))
              ?_ (dsm_load_wvec hll2 hmL) ?_
            · try simp only [LeanQbe.T.Arg.val_var]
              rw [ptr_mul4_eq, m4_zext_shl1]
            m4_wp_lets
            refine wp_load_sep_at
              (ptr := c.pWvec + BitVec.ofNat 64
                (4 * (2 * (wsL[src_off.toNat + ri.toNat]'hsR_lt).toNat)))
              ?_ (dsm_load_wvec hrl2 hmL) ?_
            · try simp only [LeanQbe.T.Arg.val_var]
              rw [ptr_mul4_eq, m4_zext_shl1]
            m4_wp_lets
            simp only [LeanQbe.T.wp_jnz, LeanQbe.T.Arg.val_var]
            refine ⟨fun hle => ?_, fun hgt => ?_⟩
            · have hle' : (wvec1[2 * (wsL[src_off.toNat + li.toNat]'hsL_lt).toNat]'hll2).toNat ≤
                  (wvec1[2 * (wsL[src_off.toNat + ri.toNat]'hsR_lt).toNat]'hrl2).toNat :=
                of_decide_eq_true hle
              m4_wp_lets
              refine wp_store_sep_at
                (ptr := c.pWsort + BitVec.ofNat 64
                  (4 * (dst_off.toNat + ki.toNat)))
                (m4_ptr_mul4_add _ _ _ (by
                  have := hinvL.2.2.2.2.2.1; m4_omega))
                (dsm_store_ws _ hdst_k hmL) fun mS hmS => ?_
              m4_wp_lets
              m4_wp_jump
              have hinv' := m4MergeInv_step_l hinvL hli_lt (by m4_omega)
                (by have := hinvL.1; m4_omega)
                (by rcases hdisj with h | h <;> m4_omega)
                hsL hll_eq
                (Nat.lt_trans hll_cv (by m4_omega))
                fun q hq1 hq2 => by
                  have := hinvL.2.2.2.1
                  have hq_ok : m4WsVal wsD q < 2 * s.core.cur_vars :=
                    hbdD_src q (by m4_omega) (by m4_omega)
                  have hr_le := hsR (src_off.toNat + ri.toNat) q
                    (by m4_omega) hq1 hq2
                  have h1 : key (wsL[src_off.toNat + li.toNat]'hsL_lt).toNat ≤
                      key (m4WsVal wsD (src_off.toNat + ri.toNat)) := by
                    unfold key m4WvecOff m4WsVal
                    rw [List.getElem?_eq_getElem
                        (show src_off.toNat + ri.toNat < wsD.length by m4_omega),
                      Option.getD_some, ← hrl_eq, List.getElem?_eq_getElem hll2,
                      List.getElem?_eq_getElem hrl2, Option.getD_some, Option.getD_some]
                    exact hle'
                  exact Nat.le_trans h1 hr_le
              have hlp : (li + (1 : BitVec 64)).toNat = li.toNat + 1 := by
                rw [BitVec.toNat_add,
                  show ((1 : BitVec 64) : BitVec 64).toNat = 1 from rfl]; m4_omega
              exact hJStep _ _ ⟨wsL.set (dst_off.toNat + ki.toNat) _,
                by rw [hlp]; exact hinv', hmS⟩
            · have hgt' : (wvec1[2 * (wsL[src_off.toNat + ri.toNat]'hsR_lt).toNat]'hrl2).toNat <
                  (wvec1[2 * (wsL[src_off.toNat + li.toNat]'hsL_lt).toNat]'hll2).toNat :=
                Nat.lt_of_not_le (of_decide_eq_false hgt)
              m4_wp_lets
              refine wp_store_sep_at
                (ptr := c.pWsort + BitVec.ofNat 64
                  (4 * (dst_off.toNat + ki.toNat)))
                (m4_ptr_mul4_add _ _ _ (by
                  have := hinvL.2.2.2.2.2.1; m4_omega))
                (dsm_store_ws _ hdst_k hmL) fun mS hmS => ?_
              m4_wp_lets
              m4_wp_jump
              have hinv' := m4MergeInv_step_r hinvL hri_lt (by m4_omega)
                (by have := hinvL.1; m4_omega)
                (by rcases hdisj with h | h <;> m4_omega)
                hsR hrl_eq
                (Nat.lt_trans hrl_cv (by m4_omega))
                fun q hq1 hq2 => by
                  have := hinvL.2.1
                  have hl_le := hsL (src_off.toNat + li.toNat) q
                    (by m4_omega) hq1 hq2
                  have h1 : key (wsL[src_off.toNat + ri.toNat]'hsR_lt).toNat ≤
                      key (m4WsVal wsD (src_off.toNat + li.toNat)) := by
                    unfold key m4WvecOff m4WsVal
                    rw [List.getElem?_eq_getElem
                        (show src_off.toNat + li.toNat < wsD.length by m4_omega),
                      Option.getD_some, ← hll_eq, List.getElem?_eq_getElem hll2,
                      List.getElem?_eq_getElem hrl2, Option.getD_some, Option.getD_some]
                    exact Nat.le_of_lt hgt'
                  exact Nat.le_trans h1 hl_le
              have hrp : (ri + (1 : BitVec 64)).toNat = ri.toNat + 1 := by
                rw [BitVec.toNat_add,
                  show ((1 : BitVec 64) : BitVec 64).toNat = 1 from rfl]; m4_omega
              exact hJStep _ _ ⟨wsL.set (dst_off.toNat + ki.toNat) _,
                by rw [hrp]; exact hinv', hmS⟩
        · have hri_ge : hi.toNat ≤ ri.toNat :=
            Nat.not_lt.mp (of_decide_eq_false hrih)
          m4_wp_jump
          exact hJExit _ _ ⟨Or.inr hri_ge, wsL, hinvL, hmL⟩
      · have hli_ge : mid.toNat ≤ li.toNat :=
          Nat.not_lt.mp (of_decide_eq_false hlim)
        m4_wp_jump
        exact hJExit _ _ ⟨Or.inl hli_ge, wsL, hinvL, hmL⟩

private theorem m4_merge_outer_wp
    {Γ : Env} {Q : Post []} {X : XPost} {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {n : Val i64} {mB : Mem 64}
    {wvec1 wsort1 wsB : List (BitVec 32)} {J7 : Cont []}
    (hmx : c.max_vars < 2 * 2 ^ 28) (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (hn_le : n.toNat ≤ 2 * s.core.cur_vars) (hn_gt1 : 1 < n.toNat)
    (h2n_le : 2 * n.toNat ≤ 2 * s.core.cur_vars)
    (hwv1 : wvec1.length = 4 * c.max_vars) (_hws1 : wsort1.length = 2 * c.max_vars)
    (hwvec_lt : 2 * (2 * s.core.cur_vars) ≤ wvec1.length)
    (hwsB : wsB.length = 2 * c.max_vars)
    (hpmB : (wsB.take n.toNat).Perm (wsort1.take n.toNat))
    (hbdB : ∀ i < n.toNat, m4WsVal wsB i < 2 * s.core.cur_vars)
    (hsrtB0 : ∀ q, 16 * q < n.toNat →
      M4Sorted (m4WvecOff wvec1) wsB (16 * q) (min (16 * q + 16) n.toNat))
    (hmB : DefragMem c s wvec1 wsB s.core.wstk R mB)
    (hJ7 : ∀ (xs : Tup Val []) (m : Mem 64),
      (∃ wsort2 : List (BitVec 32), wsort2.length = 2 * c.max_vars ∧
        (wsort2.take n.toNat).Perm (wsort1.take n.toNat) ∧
        M4Sorted (m4WvecOff wvec1) wsort2 0 n.toNat ∧
        DefragMem c s wvec1 wsort2 s.core.wstk R m) → J7 xs m) :
    wp Γ Q X (m4MergeOuterExpr c.pWvec c.pWsort n J7) mB := by
  let key := m4WvecOff wvec1
  dsimp only [m4MergeOuterExpr, m4MergeSortExpr,
    m4ExLetI64, m4ExLetBool, m4ExLdI64, m4ExJnz, m4ExGrp0, m4ExGrp1, m4ExGrp3, m4ExGrp4, m4ExGrpK0]
  m4_wp_lets
  refine wp_loop_inv
    (fun (src_off, dst_off, width, ()) mM =>
      ((src_off.toNat = 0 ∧ dst_off.toNat = n.toNat) ∨
        (src_off.toNat = n.toNat ∧ dst_off.toNat = 0)) ∧
      16 ≤ width.toNat ∧ width.toNat < 2 * n.toNat + 16 ∧
      ∃ wsM : List (BitVec 32), wsM.length = 2 * c.max_vars ∧
        ((wsM.drop src_off.toNat).take n.toNat).Perm (wsort1.take n.toNat) ∧
        (∀ p, src_off.toNat ≤ p → p < src_off.toNat + n.toNat →
          m4WsVal wsM p < 2 * s.core.cur_vars) ∧
        (∀ q, width.toNat * q < n.toNat →
          M4Sorted key wsM (src_off.toNat + width.toNat * q)
            (src_off.toNat + min (width.toNat * (q + 1)) n.toNat)) ∧
        DefragMem c s wvec1 wsM s.core.wstk R mM)
    (fun (_, _, width, ()) _ => 2 * n.toNat + 16 - width.toNat)
    (fun JM hJM => ?_) ?_
  · m4_wp_lets; m4_wp_jump
    have hz64 : ((0 : BitVec 64) : BitVec 64).toNat = 0 := rfl
    have hw16_eq : ((16 : BitVec 64) : BitVec 64).toNat = 16 := rfl
    refine hJM _ _ ⟨Or.inl ⟨hz64, rfl⟩,
      by rw [hw16_eq]; exact le_refl _, by rw [hw16_eq]; m4_omega,
      wsB, hwsB, hpmB,
      fun p hp1 hp2 => by
        rw [hz64] at hp2
        exact hbdB p (by m4_omega),
      fun q hq => by
        rw [hw16_eq] at hq
        have := hsrtB0 q hq
        intro a b ha hab hb
        rw [hz64, hw16_eq, Nat.zero_add] at ha hb
        rw [Nat.mul_add, Nat.mul_one] at hb
        exact this a b ha hab hb,
      hmB⟩
  · rintro JM ⟨src_off, dst_off, width, ⟨⟩⟩ mM
      ⟨hso_do, hw16, hw_ub, wsM, hwsM, hpmM, hbdM, hsrtM, hmM⟩ hJM
    clear wsB hwsB hpmB hbdB hsrtB0 hmB
    m4_wp_lets
    simp only [LeanQbe.T.wp_jnz, LeanQbe.T.Arg.val_var]
    refine ⟨fun hwn => ?_, fun hwn => ?_⟩
    · have hwn_lt : width.toNat < n.toNat := of_decide_eq_true hwn
      have hw2_lt : 2 * width.toNat < 2 ^ 64 := by m4_omega
      have hw2_eq : (width <<< (1 : Nat)).toNat = 2 * width.toNat :=
        m4_bv64_shl1 hw2_lt
      have hdisj : dst_off.toNat + n.toNat ≤ src_off.toNat ∨
          src_off.toNat + n.toNat ≤ dst_off.toNat := by
        rcases hso_do with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> m4_omega
      refine wp_loop_inv
        (fun (lo, ()) mD =>
          lo.toNat ≤ n.toNat + 2 * width.toNat ∧
          (∃ q, lo.toNat = 2 * width.toNat * q) ∧
          ∃ wsD : List (BitVec 32), wsD.length = 2 * c.max_vars ∧
            (∀ p, src_off.toNat ≤ p → p < src_off.toNat + n.toNat →
              wsD[p]? = wsM[p]?) ∧
            ((wsD.drop dst_off.toNat).take (min lo.toNat n.toNat)).Perm
              ((wsM.drop src_off.toNat).take (min lo.toNat n.toNat)) ∧
            (∀ p, dst_off.toNat ≤ p →
              p < dst_off.toNat + min lo.toNat n.toNat →
              m4WsVal wsD p < 2 * s.core.cur_vars) ∧
            (∀ q, 2 * width.toNat * q < min lo.toNat n.toNat →
              M4Sorted key wsD (dst_off.toNat + 2 * width.toNat * q)
                (dst_off.toNat + min (2 * width.toNat * (q + 1)) n.toNat)) ∧
            DefragMem c s wvec1 wsD s.core.wstk R mD)
        (fun (lo, ()) _ => n.toNat + 2 * width.toNat - lo.toNat)
        (fun JLo hJLo => ?_) ?_
      · m4_wp_lets; m4_wp_jump
        refine hJLo _ _ ⟨by simp, ⟨0, by simp⟩, wsM, hwsM,
          fun _ _ _ => rfl, by simp,
          fun p hp1 hp2 => by simp at hp2; m4_omega,
          fun q hq => by simp at hq, hmM⟩
      · rintro JLo ⟨lo, ⟨⟩⟩ mD ⟨hlo_le, ⟨ql, hql⟩, wsD, hwsD, hsufD, hpmD,
          hbdD, hsrtD, hmD⟩ hJLo
        m4_wp_lets
        simp only [LeanQbe.T.wp_jnz, LeanQbe.T.Arg.val_var]
        refine ⟨fun hlo_c => ?_, fun hlo_c => ?_⟩
        · have hlo_lt : lo.toNat < n.toNat := of_decide_eq_true hlo_c
          have hlow_eq : (lo + width).toNat = lo.toNat + width.toNat := by
            rw [BitVec.toNat_add]; m4_omega
          m4_wp_lets
          refine wp_join_group
            (fun (mid, ()) m1 =>
              m1 = mD ∧ mid.toNat = min (lo.toNat + width.toNat) n.toNat)
            ?_ ?_
          · rintro _ ⟨mid, ⟨⟩⟩ m1 ⟨hm1_eq, hmid_eq⟩
            have hmidw_eq : (mid + width).toNat = mid.toNat + width.toNat := by
              rw [BitVec.toNat_add]; m4_omega
            m4_wp_lets
            refine wp_join_group
              (fun (hi, ()) m2 =>
                m2 = m1 ∧ hi.toNat = min (mid.toNat + width.toNat) n.toNat)
              ?_ ?_
            · rintro _ ⟨hi, ⟨⟩⟩ m2 ⟨hm2_eq, hhi_eq⟩
              have hmD_eq : m2 = mD := hm2_eq.trans hm1_eq
              have hsrtD_src : ∀ p, src_off.toNat ≤ p →
                  p < src_off.toNat + n.toNat → wsD[p]? = wsM[p]? := hsufD
              have hm_eq_src : ∀ a b, a ≤ b → b ≤ n.toNat →
                  M4Sorted key wsM (src_off.toNat + a) (src_off.toNat + b) →
                  M4Sorted key wsD (src_off.toNat + a) (src_off.toNat + b) :=
                fun a b _ hb hsr i j hi1 hij hj1 => by
                  unfold m4WsVal
                  rw [hsufD _ (by m4_omega) (by m4_omega),
                    hsufD _ (by m4_omega) (by m4_omega)]
                  exact hsr i j hi1 hij hj1
              have hsL : M4Sorted key wsD (src_off.toNat + lo.toNat)
                  (src_off.toNat + mid.toNat) := by
                refine hm_eq_src _ _ (by m4_omega) (by m4_omega) ?_
                have h0 := hsrtM (2 * ql) (by
                  rw [Nat.mul_left_comm, ← Nat.mul_assoc, ← hql]; exact hlo_lt)
                have hmid_w : width.toNat * (2 * ql + 1) =
                    lo.toNat + width.toNat := by
                  rw [Nat.mul_add, Nat.mul_left_comm, ← Nat.mul_assoc,
                    ← hql, Nat.mul_one]
                rwa [Nat.mul_left_comm, ← Nat.mul_assoc, ← hql,
                  hmid_w, ← hmid_eq] at h0
              have hsR : M4Sorted key wsD (src_off.toNat + mid.toNat)
                  (src_off.toNat + hi.toNat) := by
                by_cases hmh : mid.toNat < hi.toNat
                · refine hm_eq_src _ _ (by m4_omega) (by m4_omega) ?_
                  have hmid_val : mid.toNat = lo.toNat + width.toNat := by
                    m4_omega
                  have h0 := hsrtM (2 * ql + 1) (by
                    rw [Nat.mul_add, Nat.mul_left_comm, ← Nat.mul_assoc,
                      ← hql, Nat.mul_one]
                    m4_omega)
                  rwa [Nat.mul_add, Nat.mul_left_comm, ← Nat.mul_assoc,
                    ← hql, Nat.mul_one,
                    ← hmid_val, show 2 * ql + 1 + 1 = 2 * ql + 2 by m4_omega,
                    Nat.mul_add, Nat.mul_left_comm, ← Nat.mul_assoc, ← hql,
                    show lo.toNat + width.toNat * 2 =
                      mid.toNat + width.toNat by m4_omega,
                    ← hhi_eq] at h0
                · intro a b ha hab hb; m4_omega
              have hbdD_src : ∀ q, src_off.toNat ≤ q →
                  q < src_off.toNat + n.toNat →
                  m4WsVal wsD q < 2 * s.core.cur_vars := fun q hq1 hq2 => by
                unfold m4WsVal; rw [hsufD q hq1 hq2]; exact hbdM q hq1 hq2
              have hmD_eq : m2 = mD := hm2_eq.trans hm1_eq
              subst hmD_eq
              exact m4_merge_pair_wp hmx hcv_le hn_le h2n_le hso_do hw16 hwn_lt hw_ub hw2_eq hdisj
                hwv1 hwvec_lt hlo_le hlo_lt hql hmid_eq hhi_eq hwsM hwsD hsufD hpmD hbdD hsrtD
                hsL hsR hbdD_src hmD fun ys m' hm hx => hJLo ys m' hm hx
            · intro JHi hJHi
              m4_wp_lets; simp only [LeanQbe.T.wp_jnz, LeanQbe.T.Arg.val_var]
              refine ⟨fun hgt => ?_, fun hle => ?_⟩
              · have := of_decide_eq_true hgt
                m4_wp_jump
                exact hJHi _ _ ⟨rfl, by simp [Nat.min_def]; m4_omega⟩
              · have := Nat.not_lt.mp (of_decide_eq_false hle)
                m4_wp_jump
                exact hJHi _ _ ⟨rfl, by rw [hmidw_eq]; m4_omega⟩
          · intro JMid hJMid
            m4_wp_lets; simp only [LeanQbe.T.wp_jnz, LeanQbe.T.Arg.val_var]
            refine ⟨fun hgt => ?_, fun hle => ?_⟩
            · have := of_decide_eq_true hgt
              m4_wp_jump
              exact hJMid _ _ ⟨rfl, by simp [Nat.min_def]; m4_omega⟩
            · have := Nat.not_lt.mp (of_decide_eq_false hle)
              m4_wp_jump
              exact hJMid _ _ ⟨rfl, by rw [hlow_eq]; m4_omega⟩
        · have hlo_ge : n.toNat ≤ lo.toNat := Nat.not_lt.mp (of_decide_eq_false hlo_c)
          have hmin_lo : min lo.toNat n.toNat = n.toNat :=
            Nat.min_eq_right hlo_ge
          rw [hmin_lo] at hpmD hbdD hsrtD
          m4_wp_lets; m4_wp_jump
          refine hJM _ _ (by dsimp only; rw [hw2_eq]; m4_omega)
            ⟨by rcases hso_do with ⟨h1, h2⟩ | ⟨h1, h2⟩
                · exact Or.inr ⟨h2, h1⟩
                · exact Or.inl ⟨h2, h1⟩,
             by rw [hw2_eq]; m4_omega, by rw [hw2_eq]; m4_omega, wsD, hwsD,
             hpmD.trans hpmM,
             fun p hp1 hp2 => hbdD p hp1 hp2,
             fun q hq => by
               rw [hw2_eq] at hq ⊢; exact hsrtD q hq, hmD⟩
    · have hwn_ge : n.toNat ≤ width.toNat := Nat.not_lt.mp (of_decide_eq_false hwn)
      clear hwn hJM JM hw16 hw_ub
      have hsrt_all : M4Sorted key wsM src_off.toNat (src_off.toNat + n.toNat) := by
        have h0 := hsrtM 0 (by simp; m4_omega)
        simpa [Nat.min_eq_right hwn_ge] using h0
      m4_wp_lets
      refine wp_join_group
        (fun _ mF => ∃ wsF : List (BitVec 32), wsF.length = 2 * c.max_vars ∧
          (wsF.take n.toNat).Perm (wsort1.take n.toNat) ∧
          M4Sorted key wsF 0 n.toNat ∧
          DefragMem c s wvec1 wsF s.core.wstk R mF)
        ?_ ?_
      · rintro _ _ mF ⟨wsF, hwsF, hpmF, hsrtF, hmF⟩
        m4_wp_lets
        m4_wp_jump
        exact hJ7 _ _ ⟨wsF, hwsF, hpmF, hsrtF, hmF⟩
      · intro JCopy hJCopy
        m4_wp_lets
        simp only [LeanQbe.T.wp_jnz, LeanQbe.T.Arg.val_var]
        refine ⟨fun hne0 => ?_, fun heq0 => ?_⟩
        · have hsrc_n : src_off.toNat = n.toNat := by
            rcases hso_do with ⟨h1, _⟩ | ⟨h1, _⟩
            · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h1))
                (of_decide_eq_true hne0)
            · exact h1
          clear hne0 hso_do dst_off
          refine wp_loop_inv
            (fun (ci, ()) mC =>
              ci.toNat ≤ n.toNat ∧ ∃ wsC : List (BitVec 32),
                wsC.length = 2 * c.max_vars ∧
                (∀ p < ci.toNat, wsC[p]? = wsM[n.toNat + p]?) ∧
                (∀ p, n.toNat ≤ p → wsC[p]? = wsM[p]?) ∧
                DefragMem c s wvec1 wsC s.core.wstk R mC)
            (fun (ci, ()) _ => n.toNat - ci.toNat)
            (fun JC hJC => ?_) ?_
          · m4_wp_lets; m4_wp_jump
            exact hJC _ _ ⟨by simp, wsM, hwsM, fun _ h => by simp at h,
              fun _ _ => rfl, hmM⟩
          · rintro JC ⟨ci, ⟨⟩⟩ mC ⟨hci_le, wsC, hwsC, hpreC, hsufC, hmC⟩ hJC
            m4_wp_lets; simp only [LeanQbe.T.wp_jnz, LeanQbe.T.Arg.val_var]
            refine ⟨fun hci => ?_, fun hci => ?_⟩
            · have hci_lt : ci.toNat < n.toNat := of_decide_eq_true hci
              have hsci_eq : (src_off + ci).toNat = n.toNat + ci.toNat := by
                rw [BitVec.toNat_add, hsrc_n]; m4_omega
              have hsci_lt : n.toNat + ci.toNat < wsC.length := by m4_omega
              have hci_ws : ci.toNat < wsC.length := by m4_omega
              have hval_eq : wsC[n.toNat + ci.toNat]'hsci_lt =
                  wsM[n.toNat + ci.toNat]'(by m4_omega) := by
                have h1 := hsufC (n.toNat + ci.toNat) (by m4_omega)
                rw [List.getElem?_eq_getElem hsci_lt,
                  List.getElem?_eq_getElem (by m4_omega)] at h1
                exact Option.some.inj h1
              m4_wp_lets
              refine wp_load_sep_at
                (ptr := c.pWsort + BitVec.ofNat 64 (4 * (n.toNat + ci.toNat)))
                (by simp only [LeanQbe.T.Arg.val_var]
                    rw [m4_ptr_mul4_add _ _ _ (by m4_omega), hsrc_n])
                (dsm_load_ws hsci_lt hmC) ?_
              m4_wp_lets
              refine wp_store_sep_at
                (ptr := c.pWsort + BitVec.ofNat 64 (4 * ci.toNat))
                (ptr_mul4_eq c.pWsort ci)
                (dsm_store_ws _ hci_ws hmC) fun mS hmS => ?_
              m4_wp_lets
              m4_wp_jump
              have hcp1 : (ci + (1 : BitVec 64)).toNat = ci.toNat + 1 := by
                rw [BitVec.toNat_add, show ((1 : BitVec 64) : BitVec 64).toNat = 1 from rfl]
                m4_omega
              refine hJC _ _ (by dsimp only; rw [hcp1]; m4_omega)
                ⟨by rw [hcp1]; m4_omega, _, by rw [List.length_set, hwsC],
                 fun p hp => ?_,
                 fun p hp => by
                   rw [List.getElem?_set_ne (by m4_omega)]; exact hsufC p hp,
                 hmS⟩
              by_cases hpci : p = ci.toNat
              · subst hpci
                simp only [LeanQbe.T.Arg.val_var]
                rw [List.getElem?_set_self hci_ws, hval_eq,
                  List.getElem?_eq_getElem (by m4_omega)]
              · rw [hcp1] at hp
                rw [List.getElem?_set_ne (Ne.symm hpci)]
                exact hpreC p (by m4_omega)
            · have hci_eq : ci.toNat = n.toNat := by
                have := Nat.not_lt.mp (of_decide_eq_false hci); m4_omega
              rw [hci_eq] at hpreC
              have heq_tk : wsC.take n.toNat = (wsM.drop n.toNat).take n.toNat := by
                simpa using m4Slice_congr (xs := wsC) (ys := wsM.drop n.toNat)
                  (off := 0) (n := n.toNat) (by m4_omega)
                  (by simp [List.length_drop]; m4_omega)
                  fun p _ hp => by
                    rw [hpreC p (by m4_omega), List.getElem?_drop]
              have hsrtC : M4Sorted key wsC 0 n.toNat := by
                intro a b ha hab hb
                unfold m4WsVal; rw [hpreC a (by m4_omega), hpreC b (by m4_omega)]
                exact hsrt_all (n.toNat + a) (n.toNat + b)
                  (by m4_omega) (by m4_omega) (by rw [hsrc_n]; m4_omega)
              m4_wp_jump
              refine hJCopy _ _ ⟨wsC, hwsC, ?_, hsrtC, hmC⟩
              rw [heq_tk]; simpa [hsrc_n] using hpmM
        · have hsrc0 : src_off.toNat = 0 := by
            have h : src_off = 0 := by simpa using heq0
            exact congrArg BitVec.toNat h
          m4_wp_jump
          refine hJCopy _ _ ⟨wsM, hwsM, by simpa [hsrc0] using hpmM,
            by simpa [hsrc0] using hsrt_all, hmM⟩

private theorem m4_mergesort_wp
    {Γ : Env} {Q : Post []} {X : XPost} {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {n : Val i64} {m1 : Mem 64}
    {wvec1 wsort1 : List (BitVec 32)} {J7 : Cont []}
    (hmx : c.max_vars < 2 * 2 ^ 28) (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (hn_le : n.toNat ≤ 2 * s.core.cur_vars) (hn_gt1 : 1 < n.toNat)
    (h2n_le : 2 * n.toNat ≤ 2 * s.core.cur_vars)
    (hwv1 : wvec1.length = 4 * c.max_vars) (hws1 : wsort1.length = 2 * c.max_vars)
    (hwvec_lt : 2 * (2 * s.core.cur_vars) ≤ wvec1.length)
    (hcov1 : M4WsCovers wsort1 n.toNat (2 * s.core.cur_vars) (fullWatchSize s))
    (hm1 : DefragMem c s wvec1 wsort1 s.core.wstk R m1)
    (hJ7 : ∀ (xs : Tup Val []) (m : Mem 64),
      (∃ wsort2 : List (BitVec 32), wsort2.length = 2 * c.max_vars ∧
        (wsort2.take n.toNat).Perm (wsort1.take n.toNat) ∧
        M4Sorted (m4WvecOff wvec1) wsort2 0 n.toNat ∧
        DefragMem c s wvec1 wsort2 s.core.wstk R m) → J7 xs m) :
    wp Γ Q X (m4MergeSortExpr c.pWvec c.pWsort n J7) m1 := by
  let key := m4WvecOff wvec1
  have hmv_ws : 2 * s.core.cur_vars ≤ wsort1.length := by m4_omega
  dsimp only [m4MergeSortExpr, m4ExLetI64, m4ExLetBool, m4ExLdI64, m4ExJnz,
    m4ExGrp0, m4ExGrp1, m4ExGrp3, m4ExGrp4, m4ExGrpK0]
  refine wp_loop_inv
    (fun (blk, ()) mB =>
      (∃ q, blk.toNat = 16 * q) ∧ blk.toNat ≤ n.toNat + 15 ∧
      ∃ wsB : List (BitVec 32), wsB.length = 2 * c.max_vars ∧
        (wsB.take n.toNat).Perm (wsort1.take n.toNat) ∧
        (∀ i < n.toNat, m4WsVal wsB i < 2 * s.core.cur_vars) ∧
        (∀ q, 16 * q < min blk.toNat n.toNat →
          M4Sorted key wsB (16 * q) (min (16 * q + 16) n.toNat)) ∧
        DefragMem c s wvec1 wsB s.core.wstk R mB)
    (fun (blk, ()) _ => n.toNat + 15 - blk.toNat)
    (fun JB hJB => ?_) ?_
  · m4_wp_lets; m4_wp_jump
    exact hJB _ _ ⟨⟨0, by simp⟩, by simp, wsort1, hws1,
      List.Perm.refl _, fun i hi => (hcov1.1 i hi).1,
      fun q hq => by simp at hq, hm1⟩
  · rintro JB ⟨blk, ⟨⟩⟩ mB ⟨⟨qb, hqb⟩, hblk_le, wsB, hwsB, hpmB, hbdB,
      hsrtB, hmB⟩ hJB
    m4_wp_lets
    simp only [LeanQbe.T.wp_jnz, LeanQbe.T.Arg.val_var]
    refine ⟨fun hbn => ?_, fun hbn => ?_⟩
    · have hbn_lt : blk.toNat < n.toNat := of_decide_eq_true hbn
      have hbn16 : (blk + (16 : BitVec 64)).toNat = blk.toNat + 16 := by
        rw [BitVec.toNat_add, show ((16 : BitVec 64) : BitVec 64).toNat = 16 from rfl]; m4_omega
      m4_wp_lets
      refine wp_join_group
        (fun (hi, ()) mH => mH = mB ∧ hi.toNat = min (blk.toNat + 16) n.toNat)
        ?_ ?_
      · rintro _ ⟨hi, ⟨⟩⟩ mH ⟨rfl, hhi_eq⟩
        m4_wp_lets
        refine wp_loop_inv
          (fun (ii, ()) mI =>
            blk.toNat + 1 ≤ ii.toNat ∧ ii.toNat ≤ hi.toNat ∧
            ∃ wsI : List (BitVec 32), wsI.length = 2 * c.max_vars ∧
              (wsI.take n.toNat).Perm (wsort1.take n.toNat) ∧
              (∀ i < n.toNat, m4WsVal wsI i < 2 * s.core.cur_vars) ∧
              (∀ p, (p < blk.toNat ∨ hi.toNat ≤ p) → wsI[p]? = wsB[p]?) ∧
              M4Sorted key wsI blk.toNat (min ii.toNat hi.toNat) ∧
              DefragMem c s wvec1 wsI s.core.wstk R mI)
          (fun (ii, ()) _ => hi.toNat - ii.toNat)
          (fun JI hJI => ?_) ?_
        · m4_wp_lets; m4_wp_jump
          have hbp1 : (blk + (1 : BitVec 64)).toNat = blk.toNat + 1 := by
            rw [BitVec.toNat_add, show ((1 : BitVec 64) : BitVec 64).toNat = 1 from rfl]; m4_omega
          refine hJI _ _ ⟨by rw [hbp1]; m4_omega,
            by rw [hbp1, hhi_eq]; exact Nat.le_min.mpr ⟨by m4_omega, hbn_lt⟩,
            wsB, hwsB, hpmB, hbdB, fun _ _ => rfl, fun a b ha hab hb => by
              rw [hbp1] at hb
              have hmin := Nat.min_le_left (blk.toNat + 1) hi.toNat
              have heq : a = b := by m4_omega
              subst heq; exact Nat.le_refl _,
            hmB⟩
        · rintro JI ⟨ii, ⟨⟩⟩ mI ⟨hii_lo, hii_hi, wsI, hwsI, hpmI, hbdI,
            hunchI, hsrtI, hmI⟩ hJI
          m4_wp_lets
          simp only [LeanQbe.T.wp_jnz, LeanQbe.T.Arg.val_var]
          refine ⟨fun hii => ?_, fun hii => ?_⟩
          · have hii_lt : ii.toNat < hi.toNat := of_decide_eq_true hii
            have hii_ws : ii.toNat < wsI.length := by m4_omega
            have hxl_cv : (wsI[ii.toNat]'hii_ws).toNat < 2 * s.core.cur_vars := by
              have := hbdI ii.toNat (by m4_omega); unfold m4WsVal at this
              rwa [List.getElem?_eq_getElem hii_ws, Option.getD_some] at this
            have hxl2_lt : 2 * (wsI[ii.toNat]'hii_ws).toNat < wvec1.length := by
              m4_omega
            have hsrtI' : M4Sorted key wsI blk.toNat ii.toNat := by
              simpa [Nat.min_eq_left (Nat.le_of_lt hii_lt)] using hsrtI
            m4_wp_lets
            refine wp_load_sep_at
              (ptr := c.pWsort + BitVec.ofNat 64 (4 * ii.toNat))
              (ptr_mul4_eq c.pWsort ii) (dsm_load_ws hii_ws hmI) ?_
            m4_wp_lets
            refine wp_load_sep_at
              (ptr := c.pWvec + BitVec.ofNat 64
                (4 * (2 * (wsI[ii.toNat]'hii_ws).toNat)))
              (by try simp only [LeanQbe.T.Arg.val_var]; rw [ptr_mul4_eq, m4_zext_shl1])
              (dsm_load_wvec hxl2_lt hmI) ?_
            let xl := wsI[ii.toNat]'hii_ws
            let xo := wvec1[2 * xl.toNat]'hxl2_lt
            m4_wp_lets
            refine wp_join_group
              (fun (jj, ()) mJ =>
                blk.toNat ≤ jj.toNat ∧ jj.toNat ≤ ii.toNat ∧
                ∃ wsJ : List (BitVec 32), wsJ.length = 2 * c.max_vars ∧
                  (∀ p, p < jj.toNat ∨ ii.toNat < p → wsJ[p]? = wsI[p]?) ∧
                  M4Sorted key wsJ (jj.toNat + 1) (ii.toNat + 1) ∧
                  (∀ p, jj.toNat < p → p ≤ ii.toNat →
                    key xl.toNat < key (m4WsVal wsJ p)) ∧
                  ((wsJ.set jj.toNat xl).take n.toNat).Perm (wsI.take n.toNat) ∧
                  (∀ p, jj.toNat < p → p ≤ ii.toNat →
                    m4WsVal wsJ p < 2 * s.core.cur_vars) ∧
                  (jj.toNat = blk.toNat ∨
                    key (m4WsVal wsJ (jj.toNat - 1)) ≤ key xl.toNat) ∧
                  DefragMem c s wvec1 wsJ s.core.wstk R mJ)
              ?_ ?_
            · rintro _ ⟨jj, ⟨⟩⟩ mJ ⟨hbj, hji, wsJ, hwsJ, hunchJ, hsrtJ, hgtJ,
                hpmJ, hbdJ, hleJ, hmJ⟩
              have hiip1 : (ii + (1 : BitVec 64)).toNat = ii.toNat + 1 := by
                rw [BitVec.toNat_add, show ((1 : BitVec 64) : BitVec 64).toNat = 1 from rfl]
                m4_omega
              m4_wp_lets
              refine wp_store_sep_at
                (ptr := c.pWsort + BitVec.ofNat 64 (4 * jj.toNat))
                (ptr_mul4_eq c.pWsort jj) (dsm_store_ws xl (by m4_omega) hmJ)
                fun mS hmS => ?_
              m4_wp_lets
              m4_wp_jump
              have hdone_s := m4Insert_sorted_done (key := key)
                (wsI := wsI) (wsJ := wsJ) (xl := xl)
                hbj hji (by m4_omega) hii_ws hunchJ hsrtI' hsrtJ hgtJ hleJ
              refine hJI _ _ (by dsimp only; rw [hiip1]; m4_omega)
                ⟨by rw [hiip1]; m4_omega, by rw [hiip1]; m4_omega,
                 wsJ.set jj.toNat xl,
                 by rw [List.length_set, hwsJ], hpmJ.trans hpmI, fun i hi => ?_,
                 fun p hp => by
                   rw [List.getElem?_set_ne (by m4_omega)]
                   exact (hunchJ p (by rcases hp with h | h <;> m4_omega)).trans
                     (hunchI p hp),
                 by rw [hiip1]
                    simpa [Nat.min_eq_left (by m4_omega : ii.toNat + 1 ≤ hi.toNat)]
                      using hdone_s,
                 hmS⟩
              by_cases hij : i = jj.toNat
              · subst hij; unfold m4WsVal
                rw [List.getElem?_set_self (by m4_omega), Option.getD_some]; exact hxl_cv
              · unfold m4WsVal; rw [List.getElem?_set_ne (Ne.symm hij)]
                by_cases hi1 : jj.toNat < i ∧ i ≤ ii.toNat
                · exact hbdJ i hi1.1 hi1.2
                · have hi_un : i < jj.toNat ∨ ii.toNat < i := by m4_omega
                  unfold m4WsVal at hbdI
                  rw [hunchJ i hi_un]; exact hbdI i hi
            · intro JJ hJJ
              refine wp_loop_inv
                (fun (jj, ()) mJ =>
                  blk.toNat ≤ jj.toNat ∧ jj.toNat ≤ ii.toNat ∧
                  ∃ wsJ : List (BitVec 32), wsJ.length = 2 * c.max_vars ∧
                    (∀ p, p < jj.toNat ∨ ii.toNat < p → wsJ[p]? = wsI[p]?) ∧
                    M4Sorted key wsJ (jj.toNat + 1) (ii.toNat + 1) ∧
                    (∀ p, jj.toNat < p → p ≤ ii.toNat →
                      key xl.toNat < key (m4WsVal wsJ p)) ∧
                    (jj.toNat < ii.toNat → ∀ a, blk.toNat ≤ a → a < jj.toNat →
                      key (m4WsVal wsI a) ≤ key (m4WsVal wsJ (jj.toNat + 1))) ∧
                    ((wsJ.set jj.toNat xl).take n.toNat).Perm (wsI.take n.toNat) ∧
                    (∀ p, jj.toNat < p → p ≤ ii.toNat →
                      m4WsVal wsJ p < 2 * s.core.cur_vars) ∧
                    DefragMem c s wvec1 wsJ s.core.wstk R mJ)
                (fun (jj, ()) _ => jj.toNat - blk.toNat)
                (fun JL hJL => ?_) ?_
              · m4_wp_lets; m4_wp_jump
                refine hJL _ _ ⟨by m4_omega, le_refl _, wsI, hwsI, fun _ _ => rfl,
                  fun a b ha hab hb => by m4_omega, fun p hp1 hp2 => by m4_omega,
                  fun h => by m4_omega,
                  by rw [List.set_getElem_self hii_ws], fun p hp1 hp2 => by m4_omega,
                  hmI⟩
              · rintro JL ⟨jj, ⟨⟩⟩ mJ ⟨hbj, hji, wsJ, hwsJ, hunchJ, hsrtJ, hgtJ,
                  hstepJ, hpmJ, hbdJ, hmJ⟩ hJL
                m4_wp_lets
                simp only [LeanQbe.T.wp_jnz, LeanQbe.T.Arg.val_var]
                refine ⟨fun hj_gt => ?_, fun hj_le => ?_⟩
                · have hjb_lt : blk.toNat < jj.toNat := of_decide_eq_true hj_gt
                  have hjm1_ws : jj.toNat - 1 < wsJ.length := by m4_omega
                  have hjm1_eq : wsJ[jj.toNat - 1]'hjm1_ws =
                      wsI[jj.toNat - 1]'(by m4_omega) := by
                    have h1 := hunchJ (jj.toNat - 1) (Or.inl (by m4_omega))
                    rw [List.getElem?_eq_getElem hjm1_ws,
                      List.getElem?_eq_getElem (by m4_omega)] at h1
                    exact Option.some.inj h1
                  have hpl_cv : (wsJ[jj.toNat - 1]'hjm1_ws).toNat <
                      2 * s.core.cur_vars := by
                    rw [hjm1_eq]; have := hbdI (jj.toNat - 1) (by m4_omega)
                    unfold m4WsVal at this
                    rwa [List.getElem?_eq_getElem (by m4_omega),
                      Option.getD_some] at this
                  have hpl2_lt : 2 * (wsJ[jj.toNat - 1]'hjm1_ws).toNat <
                      wvec1.length := by m4_omega
                  m4_wp_lets
                  refine wp_load_sep_at
                    (ptr := c.pWsort + BitVec.ofNat 64 (4 * (jj.toNat - 1)))
                    (m4_ptr_mul4_sub1 c.pWsort jj (by m4_omega))
                    (dsm_load_ws hjm1_ws hmJ) ?_
                  m4_wp_lets
                  refine wp_load_sep_at
                    (ptr := c.pWvec + BitVec.ofNat 64
                      (4 * (2 * (wsJ[jj.toNat - 1]'hjm1_ws).toNat)))
                    (by simp only [LeanQbe.T.Arg.val_var]
                        rw [ptr_mul4_eq, m4_zext_shl1])
                    (dsm_load_wvec hpl2_lt hmJ) ?_
                  m4_wp_lets
                  simp only [LeanQbe.T.wp_jnz, LeanQbe.T.Arg.val_var]
                  refine ⟨fun hple => ?_, fun hpgt => ?_⟩
                  · have hle' : (wvec1[2 * (wsJ[jj.toNat - 1]'hjm1_ws).toNat]'
                        hpl2_lt).toNat ≤ xo.toNat := of_decide_eq_true hple
                    m4_wp_jump
                    refine hJJ _ _ ⟨hbj, hji, wsJ, hwsJ, hunchJ, hsrtJ, hgtJ,
                      hpmJ, hbdJ, Or.inr ?_, hmJ⟩
                    dsimp only [xo, xl]; unfold key m4WvecOff m4WsVal
                    rw [List.getElem?_eq_getElem hjm1_ws, Option.getD_some,
                      List.getElem?_eq_getElem hpl2_lt, Option.getD_some,
                      List.getElem?_eq_getElem hxl2_lt, Option.getD_some]
                    exact hle'
                  · have hgt' : xo.toNat <
                        (wvec1[2 * (wsJ[jj.toNat - 1]'hjm1_ws).toNat]'
                          hpl2_lt).toNat :=
                      Nat.lt_of_not_le (of_decide_eq_false hpgt)
                    let pl := wsJ[jj.toNat - 1]'hjm1_ws
                    m4_wp_lets
                    refine wp_store_sep_at
                      (ptr := c.pWsort + BitVec.ofNat 64 (4 * jj.toNat))
                      (ptr_mul4_eq c.pWsort jj)
                      (dsm_store_ws pl (by m4_omega) hmJ) fun mS hmS => ?_
                    m4_wp_lets
                    m4_wp_jump
                    have hjjm1 : (jj - (1 : BitVec 64)).toNat = jj.toNat - 1 := by
                      rw [BitVec.toNat_sub,
                        show ((1 : BitVec 64) : BitVec 64).toNat = 1 from rfl]
                      have := jj.isLt; m4_omega
                    have hperm' : (((wsJ.set jj.toNat pl).set (jj.toNat - 1) xl).take
                        n.toNat).Perm (wsI.take n.toNat) :=
                      (m4Take_set_virt_perm (by m4_omega) (by m4_omega) (by m4_omega)
                        (List.getElem?_eq_getElem hjm1_ws)).trans hpmJ
                    refine hJL _ _ (by dsimp only; rw [hjjm1]; m4_omega)
                      ⟨by m4_omega, by m4_omega, wsJ.set jj.toNat pl,
                       by rw [List.length_set, hwsJ], fun p hp => ?_,
                       fun a b ha hab hb => ?_, fun p hp1 hp2 => ?_,
                       fun hlt a ha1 ha2 => ?_, by rw [hjjm1]; exact hperm',
                       fun p hp1 hp2 => ?_, hmS⟩
                    · rw [List.getElem?_set_ne (by m4_omega)]
                      exact hunchJ p (by rcases hp with h | h <;> m4_omega)
                    · have hval' : ∀ p, m4WsVal (wsJ.set jj.toNat pl) p =
                          if p = jj.toNat then pl.toNat else m4WsVal wsJ p :=
                        fun p => by
                          unfold m4WsVal; by_cases hp : p = jj.toNat
                          · subst hp
                            simp [List.getElem?_set_self
                              (by m4_omega : jj.toNat < wsJ.length)]
                          · simp [List.getElem?_set_ne (Ne.symm hp), hp]
                      rw [hjjm1, show jj.toNat - 1 + 1 = jj.toNat by m4_omega] at ha
                      rw [hval' a, hval' b]
                      by_cases haj : a = jj.toNat <;> by_cases hbj : b = jj.toNat <;>
                        simp only [haj, hbj, ↓reduceIte]
                      · exact Nat.le_refl _
                      · have hpl_eq_I : pl.toNat = m4WsVal wsI (jj.toNat - 1) := by
                          dsimp only [pl]; unfold m4WsVal; rw [hjm1_eq,
                            List.getElem?_eq_getElem (by m4_omega), Option.getD_some]
                        rw [hpl_eq_I]
                        rcases Nat.lt_or_ge jj.toNat ii.toNat with hji' | hji'
                        · have hs0 := hstepJ hji' (jj.toNat - 1) (by m4_omega)
                            (by m4_omega)
                          have hs1 := hsrtJ (jj.toNat + 1) b (by m4_omega) (by m4_omega)
                            hb
                          exact Nat.le_trans hs0 hs1
                        · m4_omega
                      · m4_omega
                      · exact hsrtJ a b (by m4_omega) hab hb
                    · rw [hjjm1] at hp1
                      by_cases hpj : p = jj.toNat
                      · subst hpj; unfold m4WsVal
                        rw [List.getElem?_set_self (by m4_omega), Option.getD_some]
                        dsimp only [xo, xl] at *; unfold key m4WvecOff
                        rw [List.getElem?_eq_getElem hpl2_lt,
                          List.getElem?_eq_getElem hxl2_lt,
                          Option.getD_some, Option.getD_some]
                        exact hgt'
                      · unfold m4WsVal; rw [List.getElem?_set_ne (Ne.symm hpj)]
                        exact hgtJ p (by m4_omega) hp2
                    · rw [hjjm1] at hlt ha2
                      rw [hjjm1, show jj.toNat - 1 + 1 = jj.toNat by m4_omega]
                      unfold m4WsVal
                      rw [List.getElem?_set_self (by m4_omega), Option.getD_some]
                      have hpl_eq_I : pl.toNat = m4WsVal wsI (jj.toNat - 1) := by
                        dsimp only [pl]; unfold m4WsVal; rw [hjm1_eq,
                          List.getElem?_eq_getElem (by m4_omega), Option.getD_some]
                      rw [hpl_eq_I]
                      exact hsrtI' a (jj.toNat - 1) ha1 (by m4_omega) (by m4_omega)
                    · rw [hjjm1] at hp1
                      by_cases hpj : p = jj.toNat
                      · subst hpj; unfold m4WsVal
                        rw [List.getElem?_set_self (by m4_omega), Option.getD_some]
                        exact hpl_cv
                      · unfold m4WsVal; rw [List.getElem?_set_ne (Ne.symm hpj)]
                        exact hbdJ p (by m4_omega) hp2
                · have hjb_eq : jj.toNat = blk.toNat := by
                    have := Nat.not_lt.mp (of_decide_eq_false hj_le); m4_omega
                  m4_wp_jump
                  exact hJJ _ _ ⟨hbj, hji, wsJ, hwsJ, hunchJ, hsrtJ, hgtJ,
                    hpmJ, hbdJ, Or.inl hjb_eq, hmJ⟩
          · have hii_eq : ii.toNat = hi.toNat := by
              have := Nat.not_lt.mp (of_decide_eq_false hii); m4_omega
            m4_wp_lets
            m4_wp_jump
            have hsrtI' : M4Sorted key wsI blk.toNat hi.toNat := by
              simpa [hii_eq] using hsrtI
            refine hJB _ _ (by dsimp only; rw [hbn16]; m4_omega)
              ⟨⟨qb + 1, by rw [hbn16]; m4_omega⟩, by rw [hbn16]; m4_omega, wsI, hwsI,
               hpmI, hbdI, fun q hq => ?_, hmI⟩
            by_cases hqq : q = qb
            · subst hqq; rw [← hqb, ← hhi_eq]; exact hsrtI'
            · have hq_lt : 16 * q < min blk.toNat n.toNat := by rw [hbn16] at hq; m4_omega
              have hp_old := hsrtB q hq_lt
              intro a b ha hab hb
              unfold m4WsVal
              rw [hunchI a (Or.inl (by m4_omega)), hunchI b (Or.inl (by m4_omega))]
              exact hp_old a b ha hab hb
      · intro JH hJH
        m4_wp_lets
        simp only [LeanQbe.T.wp_jnz, LeanQbe.T.Arg.val_var]
        refine ⟨fun hgt => ?_, fun hle => ?_⟩
        · have h1 := of_decide_eq_true hgt
          m4_wp_jump
          exact hJH _ _ ⟨rfl, by simp [Nat.min_def]; m4_omega⟩
        · have h1 := Nat.not_lt.mp (of_decide_eq_false hle)
          have hba : (blk + (16 : BitVec 64)).toNat = blk.toNat + 16 := by
            rw [BitVec.toNat_add, show ((16 : BitVec 64) : BitVec 64).toNat = 16 from rfl]
            m4_omega
          m4_wp_jump
          exact hJH _ _ ⟨rfl, by rw [hba]; m4_omega⟩
    · have hbn_ge : n.toNat ≤ blk.toNat := Nat.not_lt.mp (of_decide_eq_false hbn)
      exact m4_merge_outer_wp hmx hcv_le hn_le hn_gt1 h2n_le hwv1 hws1 hwvec_lt
        hwsB hpmB hbdB
        (fun q hq => hsrtB q (by rw [Nat.min_eq_right hbn_ge]; exact hq))
        hmB hJ7

theorem full_wstack_defrag_m4_wp (Γ : Env) :
    ∀ a m Q X, fullWstackDefragSpec a m Q X → Func.wp Γ full_wstack_defrag_m4_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hlay, hm, hQ⟩
  have hcl := hlen.core_ok; have hsl := hlen.scratch_ok
  have hmx : c.max_vars < 2 * dimacsBound := c.hmaxv; unfold dimacsBound at hmx
  have hwcap : c.wcap < 2 * dimacsBound := c.hwcap; unfold dimacsBound at hwcap
  have hcv_le := hcl.cur_vars_le
  have hwle := hcl.wlen_le; have hwvl := hcl.wvec_len; have hwsl := hcl.wstk_len_arr
  have hwsrt_l := hsl.wsort_len
  open LeanQbe.T.C0HeadStep FullArenaTactics FullIngestTactics in c0_hsteps_nogrp
  · refine hQ s.core.wvec s.core.wstk s.core.wlen s.scratch.wsort _
      ⟨{ hcl with wlen_le := hwle }, hsl⟩
      (hlay.with_wstk rfl rfl rfl rfl) id (fun _ _ => ⟨rfl, fun _ _ => rfl⟩) hm
  · have hwlen_gt1 : 1 < s.core.wlen := by
      open scoped FullArenaTactics FullIngestTactics in c0_bound
    have hwsl_pos : 0 < s.core.wstk.length := by omega
    have hnlits : (BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat)).toNat = 2 * s.core.cur_vars := by
      rw [BitVec.toNat_shiftLeft, bv64_ofNat_toNat (by omega)]
      simp [Nat.shiftLeft_eq]; omega
    clear hc
    refine wp_loop_inv
      (fun (n, l, prev_off, sorted, ()) m1 =>
        l.toNat ≤ 2 * s.core.cur_vars ∧ n.toNat ≤ l.toNat ∧
        ∃ (wvec1 wsort1 : List (BitVec 32)),
          wvec1.length = 4 * c.max_vars ∧ wsort1.length = 2 * c.max_vars ∧
          (∀ j < 2 * s.core.cur_vars, wvec1[2 * j + 1]? = s.core.wvec[2 * j + 1]?) ∧
          (∀ j < 2 * s.core.cur_vars,
            0 < fullWatchSize s j → wvec1[2 * j]? = s.core.wvec[2 * j]?) ∧
          (∀ j < l.toNat, fullWatchSize s j = 0 → wvec1[2 * j]? = some 0#32) ∧
          M4WsCovers wsort1 n.toNat l.toNat (fullWatchSize s) ∧
          (sorted = true → M4Sorted (fullWatchOff s) wsort1 0 n.toNat ∧
            (n.toNat = 0 → prev_off = 0#32) ∧
            (0 < n.toNat → prev_off.toNat = fullWatchOff s (m4WsVal wsort1 (n.toNat - 1)))) ∧
          DefragMem c s wvec1 wsort1 s.core.wstk R m1)
      (fun (_, l, _, _, ()) _ => 2 * s.core.cur_vars - l.toNat)
      (fun J hLoop => ?_) ?_
    · m4_wp_lets
      refine hLoop _ _ ⟨by simp, by simp, s.core.wvec, s.scratch.wsort, hwvl, hwsrt_l,
        fun _ _ => rfl, fun _ _ _ => rfl, fun _ hj => by simp at hj,
        ⟨fun _ hi => by simp at hi, fun _ hi => by simp at hi, fun _ hl => by simp at hl⟩,
        fun _ => ⟨fun _ _ _ _ h => by simp at h, fun _ => rfl, fun h => by simp at h⟩,
        focus_defrag hm⟩
    · rintro J ⟨n, l, prev_off, sorted, ⟨⟩⟩ m1 ⟨hl_le, hn_le, wvec1, wsort1, hwv1, hws1,
        hsz1, hoff1, hzero1, hcov1, hsort1, hm1⟩ hLoop
      clear hm
      m4_wp_lets
      try rw [LeanQbe.T.wp_jnz]
      refine ⟨fun hc => ?_, fun hc => ?_⟩
      · have hl_lt : l.toNat < 2 * s.core.cur_vars := by
          simp only [LeanQbe.T.Arg.val_var] at hc
          have := of_decide_eq_true hc; rw [hnlits] at this; exact this
        have hl2p1_lt : 2 * l.toNat + 1 < wvec1.length := by omega
        have hl2_lt : 2 * l.toNat < wvec1.length := by omega
        m4_wp_lets
        refine wp_load_sep_at (ptr := c.pWvec + BitVec.ofNat 64 (8 * l.toNat))
          (ptr_mul8_eq c.pWvec l) (dsm_load_wvec64 hl2p1_lt hm1) ?_
        m4_wp_lets
        rw [bv64_pair_hi]
        have hsz_eq : (wvec1[2 * l.toNat + 1]'hl2p1_lt).toNat = fullWatchSize s l.toNat := by
          unfold fullWatchSize fullWatchSizeCore
          have h1 := hsz1 l.toNat hl_lt; rw [← h1]
          rw [List.getElem?_eq_getElem hl2p1_lt, Option.getD_some]
        refine wp_join_group
          (fun (n', prev_off', sorted', ()) m2 =>
            n'.toNat ≤ l.toNat + 1 ∧ ∃ wvec2 wsort2 : List (BitVec 32),
              wvec2.length = 4 * c.max_vars ∧ wsort2.length = 2 * c.max_vars ∧
              (∀ j < 2 * s.core.cur_vars, wvec2[2 * j + 1]? = s.core.wvec[2 * j + 1]?) ∧
              (∀ j < 2 * s.core.cur_vars,
                0 < fullWatchSize s j → wvec2[2 * j]? = s.core.wvec[2 * j]?) ∧
              (∀ j < l.toNat + 1, fullWatchSize s j = 0 → wvec2[2 * j]? = some 0#32) ∧
              M4WsCovers wsort2 n'.toNat (l.toNat + 1) (fullWatchSize s) ∧
              (sorted' = true → M4Sorted (fullWatchOff s) wsort2 0 n'.toNat ∧
                (n'.toNat = 0 → prev_off' = 0#32) ∧
                (0 < n'.toNat →
                  prev_off'.toNat = fullWatchOff s (m4WsVal wsort2 (n'.toNat - 1)))) ∧
              DefragMem c s wvec2 wsort2 s.core.wstk R m2)
          ?_ ?_
        · rintro _ ⟨n', prev_off', sorted', ⟨⟩⟩ m2
            ⟨hn', wvec2, wsort2, hwv2, hws2, hsz2, hoff2, hzero2, hcov2, hsort2, hm2⟩
          m4_wp_lets
          m4_wp_jump
          have hlp1 : (l + (1 : BitVec 64)).toNat = l.toNat + 1 := by
            rw [BitVec.toNat_add, show ((1 : BitVec 64) : BitVec 64).toNat = 1 from rfl]
            have := l.isLt; omega
          exact hLoop _ _ (by dsimp only; omega)
            ⟨by omega, by omega, wvec2, wsort2, hwv2, hws2, hsz2, hoff2,
             by rw [hlp1]; exact hzero2, by rw [hlp1]; exact hcov2, hsort2, hm2⟩
        · intro J1 hJ1
          m4_wp_lets
          simp only [LeanQbe.T.wp_jnz, LeanQbe.T.Arg.val_var]
          refine ⟨fun hc0 => ?_, fun hc0 => ?_⟩
          · have hz_wvec : wvec1[2 * l.toNat + 1]'hl2p1_lt = 0#32 := of_decide_eq_true hc0
            have hsz0 : fullWatchSize s l.toNat = 0 := by rw [← hsz_eq, hz_wvec]; rfl
            m4_wp_lets
            refine wp_join_group
              (fun _ m2 => ∃ wvec2 : List (BitVec 32), wvec2.length = 4 * c.max_vars ∧
                (∀ j < 2 * s.core.cur_vars, wvec2[2 * j + 1]? = s.core.wvec[2 * j + 1]?) ∧
                (∀ j < 2 * s.core.cur_vars,
                  0 < fullWatchSize s j → wvec2[2 * j]? = s.core.wvec[2 * j]?) ∧
                (∀ j < l.toNat + 1, fullWatchSize s j = 0 → wvec2[2 * j]? = some 0#32) ∧
                DefragMem c s wvec2 wsort1 s.core.wstk R m2)
              ?_ ?_
            · rintro _ _ m2 ⟨wvec2, hwv2, hsz2, hoff2, hzero2, hm2⟩
              m4_wp_lets
              m4_wp_jump
              refine hJ1 _ _ ⟨by omega, wvec2, wsort1, hwv2, hws1, hsz2, hoff2, hzero2,
                ⟨fun i hi => ⟨by have := (hcov1.1 i hi).1; omega, (hcov1.1 i hi).2⟩, hcov1.2.1,
                 fun j hj hzj => hcov1.2.2 j
                   (if hjl : j = l.toNat then by subst hjl; omega else by omega) hzj⟩,
                hsort1, hm2⟩
            · intro JZ hJZ
              m4_wp_lets
              rw [bv64_pair_lo]
              simp only [LeanQbe.T.wp_jnz, LeanQbe.T.Arg.val_var]
              refine ⟨fun hne0 => ?_, fun heq0 => ?_⟩
              · m4_wp_lets
                refine wp_store_sep_at (ptr := c.pWvec + BitVec.ofNat 64 (8 * l.toNat))
                  (ptr_mul8_eq c.pWvec l) (dsm_store_wvec64_zero hl2p1_lt hz_wvec hm1)
                  fun m2 hm2 => ?_
                m4_wp_jump
                have hset := m4Wvec_set_even_eq (wvec := wvec1) (l := l.toNat) (v := 0#32) hl2_lt
                refine hJZ _ _ ⟨_, by rw [List.length_set, hwv1],
                  fun j hj => (hset j).1.trans (hsz1 j hj),
                  fun j hj hp =>
                    ((hset j).2.1 fun heq => by subst heq; omega).trans (hoff1 j hj hp),
                  fun j hj hzj => by
                    by_cases hjl : j = l.toNat
                    · subst hjl; exact (hset l.toNat).2.2
                    · exact ((hset j).2.1 hjl).trans (hzero1 j (by omega) hzj),
                  hm2⟩
              · have hlo_z : wvec1[2 * l.toNat]'hl2_lt = 0#32 := by
                  simpa using heq0
                m4_wp_jump
                refine hJZ _ _ ⟨wvec1, hwv1, hsz1, hoff1, fun j hj hzj => ?_, hm1⟩
                by_cases hjl : j = l.toNat
                · subst hjl; rw [List.getElem?_eq_getElem hl2_lt, hlo_z]
                · exact hzero1 j (by omega) hzj
          · have hszp : 0 < fullWatchSize s l.toNat := by
              have hne : wvec1[2 * l.toNat + 1]'hl2p1_lt ≠ 0#32 := of_decide_eq_false hc0
              rw [← hsz_eq]; exact Nat.pos_of_ne_zero fun h0 => hne (BitVec.eq_of_toNat_eq h0)
            have hn_ws : n.toNat < wsort1.length := by omega
            have hoff_eq : (wvec1[2 * l.toNat]'hl2_lt).toNat = fullWatchOff s l.toNat := by
              unfold fullWatchOff fullWatchOffCore
              rw [← Option.getD_some (a := wvec1[2 * l.toNat]'hl2_lt),
                ← List.getElem?_eq_getElem hl2_lt, hoff1 l.toNat hl_lt hszp]
            m4_wp_lets
            refine wp_store_sep_at (ptr := c.pWsort + BitVec.ofNat 64 (4 * n.toNat))
              (ptr_mul4_eq c.pWsort n) (dsm_store_ws (l.setWidth 32) hn_ws hm1)
              fun m2 hm2 => ?_
            have hnp1 : (n + (1 : BitVec 64)).toNat = n.toNat + 1 := by
              rw [BitVec.toNat_add, show ((1 : BitVec 64) : BitVec 64).toNat = 1 from rfl]
              have := n.isLt; omega
            have htr : (l.setWidth 32).toNat = l.toNat := by
              rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
            have hws_at : ∀ k, m4WsVal (wsort1.set n.toNat (l.setWidth 32)) k =
                if k = n.toNat then l.toNat else m4WsVal wsort1 k := fun k => by
              unfold m4WsVal; by_cases hk : k = n.toNat
              · subst hk; rw [List.getElem?_set_self hn_ws, Option.getD_some, htr]; simp
              · rw [List.getElem?_set_ne (Ne.symm hk)]; simp [hk]
            have hcov2 : M4WsCovers (wsort1.set n.toNat (l.setWidth 32))
                (n.toNat + 1) (l.toNat + 1) (fullWatchSize s) :=
              ⟨fun i hi => by
                 rw [hws_at]; split
                 · exact ⟨by omega, hszp⟩
                 · have := hcov1.1 i (by omega); exact ⟨by omega, this.2⟩,
               fun a ha b hb hab => by
                 rw [hws_at, hws_at]; split <;> split
                 · omega
                 · have := (hcov1.1 b (by omega)).1; omega
                 · have := (hcov1.1 a (by omega)).1; omega
                 · exact hcov1.2.1 a (by omega) b (by omega) hab,
               fun j hj hzj => by
                 by_cases hjl : j = l.toNat
                 · subst hjl; exact ⟨n.toNat, by omega, by rw [hws_at]; simp⟩
                 · obtain ⟨i, hi, hij⟩ := hcov1.2.2 j (by omega) hzj
                   exact ⟨i, by omega, by rw [hws_at]; simp [show i ≠ n.toNat by omega]; exact hij⟩⟩
            m4_wp_lets
            refine wp_join_group
              (fun (sorted', ()) m3 =>
                m3 = m2 ∧ (sorted' = true →
                  M4Sorted (fullWatchOff s) (wsort1.set n.toNat (l.setWidth 32)) 0 (n.toNat + 1) ∧
                  (wvec1[2 * l.toNat]'hl2_lt).toNat =
                    fullWatchOff s (m4WsVal (wsort1.set n.toNat (l.setWidth 32)) n.toNat)))
              ?_ ?_
            · rintro _ ⟨sorted', ⟨⟩⟩ m3 ⟨rfl, hsrt_ok⟩
              m4_wp_lets
              m4_wp_jump
              refine hJ1 _ _ ⟨by rw [hnp1]; omega, wvec1, wsort1.set n.toNat (l.setWidth 32),
                hwv1, by rw [List.length_set, hws1], hsz1, hoff1,
                fun j hj hzj => hzero1 j (if hjl : j = l.toNat then by subst hjl; omega
                  else by omega) hzj,
                by rwa [hnp1], fun hst => ?_, hm2⟩
              obtain ⟨hsrt', hoff_last⟩ := hsrt_ok hst
              rw [hnp1]
              exact ⟨hsrt', fun hn0 => by omega, fun _ => by
                rw [bv64_pair_lo, show n.toNat + 1 - 1 = n.toNat by omega, ← hoff_last]⟩
            · intro JS hJS
              m4_wp_lets
              rw [bv64_pair_lo]
              simp only [LeanQbe.T.wp_jnz, LeanQbe.T.Arg.val_var]
              refine ⟨fun _ => ?_, fun hge => ?_⟩
              · m4_wp_jump
                exact hJS _ _ ⟨rfl, fun htf => absurd htf Bool.false_ne_true⟩
              · have hle_prev : prev_off.toNat ≤ (wvec1[2 * l.toNat]'hl2_lt).toNat :=
                  Nat.not_lt.mp (of_decide_eq_false hge)
                m4_wp_jump
                refine hJS _ _ ⟨rfl, fun hst => ?_⟩
                obtain ⟨hsrt_p, h0_p, hlast_p⟩ := hsort1 hst
                refine ⟨fun a b ha hab hb => ?_, ?_⟩
                · rw [hws_at a, hws_at b]; split <;> split
                  · exact Nat.le_refl _
                  · omega
                  · next ha_ne hb_eq =>
                    have ha_lt : a < n.toNat := by omega
                    rcases Nat.eq_zero_or_pos n.toNat with hn0 | hn_pos
                    · omega
                    · have h1 := hsrt_p a (n.toNat - 1) ha (by omega) (by omega)
                      have h2 := hlast_p hn_pos
                      omega
                  · exact hsrt_p a b ha hab (by omega)
                · rw [hws_at]; simp [hoff_eq]
      · have hl_eq : l.toNat = 2 * s.core.cur_vars := by
          simp only [LeanQbe.T.Arg.val_var] at hc
          have := Nat.not_lt.mp (of_decide_eq_false hc); rw [hnlits] at this; omega
        rw [hl_eq] at hzero1 hcov1 hn_le
        clear hc hLoop J hl_le hl_eq
        m4_wp_lets
        try clear l
        try rw [LeanQbe.T.wp_jnz]
        refine ⟨fun hc0 => ?_, fun hc0 => ?_⟩
        · have hn0 : n.toNat = 0 := by
            simp only [LeanQbe.T.Arg.val_var] at hc0
            rw [of_decide_eq_true hc0]; rfl
          have hm1' := unfocus_defrag hm1
          dsimp only at hm1'
          let s0 : FullState :=
            { s with core := { s.core with wvec := wvec1 },
                     scratch := { s.scratch with wsort := wsort1 } }
          have hwv1' : s0.LengthsOk c :=
            ⟨{ hcl with wvec_len := hwv1 }, { hsl with wsort_len := hws1 }⟩
          open LeanQbe.T.C0HeadStep FullArenaTactics FullIngestTactics in c0_hsteps_nogrp
          have hfin := m4Defrag_finalize (s := s) (wvecC := wvec1) (wstkC := s.core.wstk.set 0 0#32)
            (wsort2 := wsort1) (n := 0) (p := 1) hlay (by simpa [hn0] using hcov1) (by omega)
            (fun j hj => by have := hsz1 j hj; unfold fullWatchSize fullWatchSizeCore; rw [this])
            (fun j hj hz => by rw [hzero1 j hj hz]; rfl) (fun _ _ => by omega) (fun _ _ => by omega)
          refine hQ wvec1 (s.core.wstk.set 0 0#32) 1 wsort1 _
            ⟨{ hcl with wvec_len := hwv1, wstk_len_arr := by simp [hwsl],
                        wlen_le := by dsimp only; omega }, { hsl with wsort_len := hws1 }⟩
            hfin.1 (fun _ => by omega) hfin.2 hm
        · have hn_pos : 0 < n.toNat := by
            simp only [LeanQbe.T.Arg.val_var] at hc0
            exact Nat.pos_of_ne_zero fun h0 =>
              absurd (BitVec.eq_of_toNat_eq (by simpa using h0)) (of_decide_eq_false hc0)
          clear hc0
          refine wp_join_group
            (fun _ m2 => ∃ wsort2 : List (BitVec 32), wsort2.length = 2 * c.max_vars ∧
              M4WsCovers wsort2 n.toNat (2 * s.core.cur_vars) (fullWatchSize s) ∧
              M4Sorted (fullWatchOff s) wsort2 0 n.toNat ∧
              DefragMem c s wvec1 wsort2 s.core.wstk R m2)
            ?_ ?_
          · rintro _ _ m2 ⟨wsort2, hws2, hcov2, hsrt2, hm2⟩
            m4_wp_lets
            try clear hm1 wsort1 hws1 hcov1 hsort1 prev_off sorted
            refine wp_loop_inv
              (fun (p, i, ()) mC =>
                1 ≤ p.toNat ∧ p.toNat ≤ s.core.wlen ∧ i.toNat ≤ n.toNat ∧
                (i.toNat < n.toNat → p.toNat ≤ fullWatchOff s (m4WsVal wsort2 i.toNat)) ∧
                ∃ wvecC wstkC : List (BitVec 32), wvecC.length = 4 * c.max_vars ∧
                  wstkC.length = c.wcap ∧
                  (∀ j < 2 * s.core.cur_vars,
                    (wvecC[2 * j + 1]?.getD 0#32).toNat = fullWatchSize s j) ∧
                  (∀ j < 2 * s.core.cur_vars,
                    fullWatchSize s j = 0 → (wvecC[2 * j]?.getD 0#32).toNat = 0) ∧
                  (∀ j < i.toNat, let l := m4WsVal wsort2 j
                    let off := (wvecC[2 * l]?.getD 0#32).toNat
                    1 ≤ off ∧ off + fullWatchSize s l ≤ p.toNat ∧
                    ∀ k < fullWatchSize s l, wstkC[off + k]? = s.core.wstk[fullWatchOff s l + k]?) ∧
                  (∀ a < i.toNat, ∀ b < i.toNat, a ≠ b →
                    let la := m4WsVal wsort2 a; let lb := m4WsVal wsort2 b
                    (wvecC[2 * la]?.getD 0#32).toNat + fullWatchSize s la ≤
                      (wvecC[2 * lb]?.getD 0#32).toNat ∨
                    (wvecC[2 * lb]?.getD 0#32).toNat + fullWatchSize s lb ≤
                      (wvecC[2 * la]?.getD 0#32).toNat) ∧
                  (∀ j, i.toNat ≤ j → j < n.toNat → let l := m4WsVal wsort2 j
                    (wvecC[2 * l]?.getD 0#32).toNat = fullWatchOff s l ∧
                    ∀ k < fullWatchSize s l,
                      wstkC[fullWatchOff s l + k]? = s.core.wstk[fullWatchOff s l + k]?) ∧
                  DefragMem c s wvecC wsort2 wstkC R mC)
              (fun (_, i, ()) _ => n.toNat - i.toNat) (fun JC hLoopC => ?_) ?_
            · m4_wp_lets
              refine hLoopC _ _ ⟨by simp, by simp; omega, by simp, fun h0 => ?_, wvec1,
                s.core.wstk, hwv1, hwsl,
                fun j hj => by unfold fullWatchSize fullWatchSizeCore; rw [hsz1 j hj],
                fun j hj hz => by rw [hzero1 j hj hz]; rfl,
                fun _ hj => by simp at hj, fun _ ha => by simp at ha,
                fun j _ hjn => ⟨by have := hcov2.1 j hjn
                                   unfold fullWatchOff fullWatchOffCore; rw [hoff1 _ this.1 this.2],
                  fun _ _ => rfl⟩, hm2⟩
              have := hcov2.1 0 (by simpa using h0); simpa using hlay.pos_off _ this.1 this.2
            · rintro JC ⟨p, i, ⟨⟩⟩ mC ⟨hp1, hple, hile, hp_off, wvecC, wstkC,
                hwvC, hwsC, hszC, hzeroC, hdoneC, hdisjC, hremC, hmC⟩ hLoopC
              clear hm2
              m4_wp_lets
              try rw [LeanQbe.T.wp_jnz]
              refine ⟨fun hc => ?_, fun hc => ?_⟩
              · have hi_lt : i.toNat < n.toNat := by
                  simp only [LeanQbe.T.Arg.val_var] at hc
                  exact of_decide_eq_true hc
                have hi_ws : i.toNat < wsort2.length := by omega
                have hlit_info := hcov2.1 i.toNat hi_lt
                have hlit_eq : (wsort2[i.toNat]'hi_ws).toNat = m4WsVal wsort2 i.toNat := by
                  unfold m4WsVal; rw [List.getElem?_eq_getElem hi_ws, Option.getD_some]
                have hlit2_lt : 2 * m4WsVal wsort2 i.toNat < wvecC.length := by omega
                have hlit2p1_lt : 2 * m4WsVal wsort2 i.toNat + 1 < wvecC.length := by omega
                have hoff_i : (wvecC[2 * m4WsVal wsort2 i.toNat]'hlit2_lt).toNat =
                    fullWatchOff s (m4WsVal wsort2 i.toNat) := by
                  rw [← (hremC i.toNat (by omega) hi_lt).1,
                    List.getElem?_eq_getElem hlit2_lt, Option.getD_some]
                have hsz_i : (wvecC[2 * m4WsVal wsort2 i.toNat + 1]'hlit2p1_lt).toNat =
                    fullWatchSize s (m4WsVal wsort2 i.toNat) := by
                  rw [← hszC (m4WsVal wsort2 i.toNat) hlit_info.1,
                    List.getElem?_eq_getElem hlit2p1_lt, Option.getD_some]
                have hp_le_off : p.toNat ≤ fullWatchOff s (m4WsVal wsort2 i.toNat) := hp_off hi_lt
                have hoff_sz_le : fullWatchOff s (m4WsVal wsort2 i.toNat) +
                    fullWatchSize s (m4WsVal wsort2 i.toNat) ≤ s.core.wlen :=
                  hlay.bounds _ hlit_info.1
                m4_wp_lets
                refine wp_load_sep_at (ptr := c.pWsort + BitVec.ofNat 64 (4 * i.toNat))
                  (ptr_mul4_eq c.pWsort i) (dsm_load_ws hi_ws hmC) ?_
                m4_wp_lets
                refine wp_load_sep_at
                  (ptr := c.pWvec + BitVec.ofNat 64 (4 * (2 * m4WsVal wsort2 i.toNat)))
                  (by simp only [LeanQbe.T.Arg.val_var]
                      rw [ptr_mul4_eq, m4_zext_shl1, hlit_eq])
                  (dsm_load_wvec hlit2_lt hmC) ?_
                m4_wp_lets
                refine wp_load_sep_at
                  (ptr := c.pWvec + BitVec.ofNat 64 (4 * (2 * m4WsVal wsort2 i.toNat + 1)))
                  (by simp only [LeanQbe.T.Arg.val_var]
                      rw [m4_ptr_mul4_zext_shl1_add1, hlit_eq])
                  (dsm_load_wvec hlit2p1_lt hmC) ?_
                m4_wp_lets
                refine wp_join_group
                  (fun _ mD => ∃ wvecD wstkD : List (BitVec 32),
                    wvecD.length = 4 * c.max_vars ∧ wstkD.length = c.wcap ∧
                    (∀ j < 2 * s.core.cur_vars,
                      (wvecD[2 * j + 1]?.getD 0#32).toNat = fullWatchSize s j) ∧
                    (∀ j < 2 * s.core.cur_vars,
                      fullWatchSize s j = 0 → (wvecD[2 * j]?.getD 0#32).toNat = 0) ∧
                    (∀ j < i.toNat + 1, let l := m4WsVal wsort2 j
                      let off := (wvecD[2 * l]?.getD 0#32).toNat
                      1 ≤ off ∧
                      off + fullWatchSize s l ≤ p.toNat + fullWatchSize s (m4WsVal wsort2 i.toNat) ∧
                      ∀ k < fullWatchSize s l,
                        wstkD[off + k]? = s.core.wstk[fullWatchOff s l + k]?) ∧
                    (∀ a < i.toNat + 1, ∀ b < i.toNat + 1, a ≠ b →
                      let la := m4WsVal wsort2 a; let lb := m4WsVal wsort2 b
                      (wvecD[2 * la]?.getD 0#32).toNat + fullWatchSize s la ≤
                        (wvecD[2 * lb]?.getD 0#32).toNat ∨
                      (wvecD[2 * lb]?.getD 0#32).toNat + fullWatchSize s lb ≤
                        (wvecD[2 * la]?.getD 0#32).toNat) ∧
                    (∀ j, i.toNat + 1 ≤ j → j < n.toNat → let l := m4WsVal wsort2 j
                      (wvecD[2 * l]?.getD 0#32).toNat = fullWatchOff s l ∧
                      ∀ k < fullWatchSize s l,
                        wstkD[fullWatchOff s l + k]? = s.core.wstk[fullWatchOff s l + k]?) ∧
                    DefragMem c s wvecD wsort2 wstkD R mD)
                  ?_ ?_
                · rintro _ _ mD ⟨wvecD, wstkD, hwvD, hwsD, hszD, hzeroD,
                    hdoneD, hdisjD, hremD, hmD⟩
                  clear hmC hszC hzeroC hdoneC hdisjC hremC
                  m4_wp_lets
                  m4_wp_jump
                  have hp_next :
                      (p + (wvecC[2 * m4WsVal wsort2 i.toNat + 1]'hlit2p1_lt).setWidth 64).toNat =
                        p.toNat + fullWatchSize s (m4WsVal wsort2 i.toNat) := by
                    rw [BitVec.toNat_add, m4_bv32_zext64, hsz_i]; omega
                  have hi_next : (i + (1 : BitVec 64)).toNat = i.toNat + 1 := by
                    rw [BitVec.toNat_add, show ((1 : BitVec 64) : BitVec 64).toNat = 1 from rfl]
                    have := i.isLt; omega
                  refine hLoopC _ _ (by dsimp only; rw [hi_next]; omega)
                    ⟨by rw [hp_next]; omega, by rw [hp_next]; omega, by rw [hi_next]; omega,
                     fun hlt => ?_, wvecD, wstkD, hwvD, hwsD, hszD,
                     hzeroD, by rw [hi_next, hp_next]; exact hdoneD,
                     by rw [hi_next]; exact hdisjD, by rw [hi_next]; exact hremD, hmD⟩
                  rw [hp_next, hi_next]
                  rw [hi_next] at hlt
                  have hgap := m4Defrag_sorted_gap hlay hcov2 hsrt2 (i := i.toNat)
                    (j := i.toNat + 1) (by omega) hlt
                  omega
                · intro JD hJD
                  clear hLoopC hQ hlen hcl hsl hsz1 hoff1 hzero1 hwv1 hwsl hwvl hwsrt_l
                    hwlen_gt1 hwsl_pos hnlits
                  m4_wp_lets
                  simp only [LeanQbe.T.wp_jnz, LeanQbe.T.Arg.val_var]
                  refine ⟨fun hne => ?_, fun heq => ?_⟩
                  · have hp_lt_off : p.toNat < fullWatchOff s (m4WsVal wsort2 i.toNat) := by
                      have hne' : p.toNat ≠ fullWatchOff s (m4WsVal wsort2 i.toNat) := fun he => by
                        apply bne_iff_ne.mp hne
                        apply BitVec.eq_of_toNat_eq; rw [m4_bv32_zext64, hoff_i, he]
                      omega
                    clear hne
                    refine wp_loop_inv
                      (fun (k, ()) mK =>
                        k.toNat ≤ fullWatchSize s (m4WsVal wsort2 i.toNat) ∧
                        ∃ wstkK : List (BitVec 32), wstkK.length = c.wcap ∧
                          (∀ idx < p.toNat, wstkK[idx]? = wstkC[idx]?) ∧
                          (∀ idx, p.toNat + fullWatchSize s (m4WsVal wsort2 i.toNat) ≤ idx →
                            wstkK[idx]? = wstkC[idx]?) ∧
                          (∀ r < k.toNat, wstkK[p.toNat + r]? =
                            s.core.wstk[fullWatchOff s (m4WsVal wsort2 i.toNat) + r]?) ∧
                          (∀ r, k.toNat ≤ r → r < fullWatchSize s (m4WsVal wsort2 i.toNat) →
                            wstkK[fullWatchOff s (m4WsVal wsort2 i.toNat) + r]? =
                            s.core.wstk[fullWatchOff s (m4WsVal wsort2 i.toNat) + r]?) ∧
                          DefragMem c s wvecC wsort2 wstkK R mK)
                      (fun (k, ()) _ => fullWatchSize s (m4WsVal wsort2 i.toNat) - k.toNat)
                      (fun JK hLoopK => ?_) ?_
                    · m4_wp_lets; m4_wp_jump
                      exact hLoopK _ _ ⟨by simp, wstkC, hwsC, fun _ _ => rfl, fun _ _ => rfl,
                        fun _ hr => by simp at hr,
                        fun r _ hr => (hremC i.toNat (by omega) hi_lt).2 r hr, hmC⟩
                    · rintro JK ⟨k, ⟨⟩⟩ mK ⟨hk_le, wstkK, hwsK, hpreK, hpostK, hcopK, hsrcK, hmK⟩
                        hLoopK
                      clear hmC
                      m4_wp_lets
                      simp only [LeanQbe.T.wp_jnz, LeanQbe.T.Arg.val_var]
                      refine ⟨fun hck => ?_, fun hck => ?_⟩
                      · have hk_lt : k.toNat < fullWatchSize s (m4WsVal wsort2 i.toNat) := by
                          have := of_decide_eq_true hck
                          rw [m4_bv32_zext64, hsz_i] at this; exact this
                        have hkp1 : (k + (1 : BitVec 64)).toNat = k.toNat + 1 := by
                          rw [BitVec.toNat_add,
                            show ((1 : BitVec 64) : BitVec 64).toNat = 1 from rfl]; omega
                        have hpk : (p + k).toNat = p.toNat + k.toNat := by
                          rw [BitVec.toNat_add]; omega
                        have hok :
                            ((wvecC[2 * m4WsVal wsort2 i.toNat]'hlit2_lt).setWidth 64 + k).toNat =
                              fullWatchOff s (m4WsVal wsort2 i.toNat) + k.toNat := by
                          rw [BitVec.toNat_add, m4_bv32_zext64, hoff_i]; omega
                        have hpk_len : p.toNat + k.toNat < wstkK.length := by omega
                        have hok_len : fullWatchOff s (m4WsVal wsort2 i.toNat) + k.toNat <
                            wstkK.length := by omega
                        m4_wp_lets
                        refine wp_load_sep_at
                          (ptr := c.pWstk + BitVec.ofNat 64
                            (4 * (fullWatchOff s (m4WsVal wsort2 i.toNat) + k.toNat)))
                          (by simp only [LeanQbe.T.Arg.val_var]; rw [ptr_mul4_eq, hok])
                          (dsm_load_wstk hok_len hmK) ?_
                        m4_wp_lets
                        refine wp_store_sep_at
                          (ptr := c.pWstk + BitVec.ofNat 64 (4 * (p.toNat + k.toNat)))
                          (by simp only [LeanQbe.T.Arg.val_var]; rw [ptr_mul4_eq, hpk])
                          (dsm_store_wstk _ hpk_len hmK) fun mK' hmK' => ?_
                        m4_wp_lets
                        m4_wp_jump
                        refine hLoopK _ _ (by dsimp only; omega)
                          ⟨by omega, _, by rw [List.length_set, hwsK],
                           fun idx hidx => by
                             rw [List.getElem?_set_ne (by omega)]; exact hpreK idx hidx,
                           fun idx hidx => by
                             rw [List.getElem?_set_ne (by omega)]; exact hpostK idx hidx,
                           fun r hr => ?_, fun r _ hr2 => by
                             rw [List.getElem?_set_ne (by omega)]; exact hsrcK r (by omega) hr2,
                           hmK'⟩
                        by_cases hrk : r = k.toNat
                        · subst hrk; rw [List.getElem?_set_self hpk_len]
                          simp only [LeanQbe.T.Arg.val_var]
                          rw [← List.getElem?_eq_getElem hok_len]
                          exact hsrcK k.toNat (by omega) hk_lt
                        · rw [List.getElem?_set_ne (by omega)]; exact hcopK r (by omega)
                      · have hk_eq : k.toNat = fullWatchSize s (m4WsVal wsort2 i.toNat) := by
                          have := Nat.not_lt.mp (of_decide_eq_false hck)
                          rw [m4_bv32_zext64, hsz_i] at this; omega
                        have hp32 : (p.setWidth 32).toNat = p.toNat := by
                          rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
                        have hset := m4Wvec_set_even_eq (wvec := wvecC)
                          (l := m4WsVal wsort2 i.toNat) (v := p.setWidth 32) hlit2_lt
                        m4_wp_lets
                        refine wp_store_sep_at
                          (ptr := c.pWvec + BitVec.ofNat 64 (4 * (2 * m4WsVal wsort2 i.toNat)))
                          (by simp only [LeanQbe.T.Arg.val_var]
                              rw [ptr_mul4_eq, m4_zext_shl1, hlit_eq])
                          (dsm_store_wvec (p.setWidth 32) hlit2_lt hmK) fun mD hmD => ?_
                        m4_wp_jump
                        refine hJD _ _ ⟨_, wstkK, by rw [List.length_set, hwvC], hwsK,
                          fun j hj => by rw [(hset j).1]; exact hszC j hj,
                          fun j hj hzj => by
                            have hne' : j ≠ m4WsVal wsort2 i.toNat := fun heq => by
                              subst heq; have := hlit_info.2; omega
                            rw [(hset j).2.1 hne']; exact hzeroC j hj hzj,
                          ?_, ?_, ?_, hmD⟩
                        · intro j hj; dsimp only
                          by_cases hji : j = i.toNat
                          · subst hji; rw [(hset 0).2.2, Option.getD_some, hp32]
                            exact ⟨hp1, by omega, fun r hr => hcopK r (by omega)⟩
                          · have hne' : m4WsVal wsort2 j ≠ m4WsVal wsort2 i.toNat :=
                              hcov2.2.1 j (by omega) i.toNat hi_lt hji
                            rw [(hset _).2.1 hne']; have hd := hdoneC j (by omega)
                            exact ⟨hd.1, by omega, fun r hr => by
                              rw [hpreK _ (by omega)]; exact hd.2.2 r hr⟩
                        · intro a ha b hb hab; dsimp only
                          by_cases hai : a = i.toNat
                          · subst hai; have hne' := hcov2.2.1 b (by omega) i.toNat hi_lt (by omega)
                            rw [(hset 0).2.2, (hset _).2.1 hne', Option.getD_some, hp32]
                            exact Or.inr (hdoneC b (by omega)).2.1
                          · by_cases hbi : b = i.toNat
                            · subst hbi
                              have hne' := hcov2.2.1 a (by omega) i.toNat hi_lt (by omega)
                              rw [(hset 0).2.2, (hset _).2.1 hne', Option.getD_some, hp32]
                              exact Or.inl (hdoneC a (by omega)).2.1
                            · have hna := hcov2.2.1 a (by omega) i.toNat hi_lt hai
                              have hnb := hcov2.2.1 b (by omega) i.toNat hi_lt hbi
                              rw [(hset _).2.1 hna, (hset _).2.1 hnb]
                              exact hdisjC a (by omega) b (by omega) hab
                        · intro j hj1 hj2; dsimp only
                          have hne' := hcov2.2.1 j hj2 i.toNat hi_lt (by omega)
                          rw [(hset _).2.1 hne']
                          have hgap := m4Defrag_sorted_gap hlay hcov2 hsrt2 (i := i.toNat) (j := j)
                            (by omega) hj2
                          have hr := hremC j (by omega) hj2
                          exact ⟨hr.1, fun r hr' => by rw [hpostK _ (by omega)]; exact hr.2 r hr'⟩
                  · have hoff_eq_p : fullWatchOff s (m4WsVal wsort2 i.toNat) = p.toNat := by
                      have h : (wvecC[2 * m4WsVal wsort2 i.toNat]'hlit2_lt).setWidth 64 = p := by
                        simpa using heq
                      have h' := congrArg BitVec.toNat h
                      rwa [m4_bv32_zext64, hoff_i] at h'
                    m4_wp_jump
                    refine hJD _ _ ⟨wvecC, wstkC, hwvC, hwsC, hszC, hzeroC, ?_, ?_,
                      fun j hj1 hj2 => hremC j (by omega) hj2, hmC⟩
                    · intro j hj; dsimp only
                      by_cases hji : j = i.toNat
                      · subst hji; have hr := hremC i.toNat (by omega) hi_lt
                        rw [hr.1, hoff_eq_p]
                        exact ⟨hp1, by omega, fun r hr' => by rw [← hoff_eq_p]; exact hr.2 r hr'⟩
                      · have hd := hdoneC j (by omega); exact ⟨hd.1, by omega, hd.2.2⟩
                    · intro a ha b hb hab; dsimp only
                      by_cases hai : a = i.toNat
                      · subst hai; rw [(hremC i.toNat (by omega) hi_lt).1, hoff_eq_p]
                        exact Or.inr (hdoneC b (by omega)).2.1
                      · by_cases hbi : b = i.toNat
                        · subst hbi; rw [(hremC i.toNat (by omega) hi_lt).1, hoff_eq_p]
                          exact Or.inl (hdoneC a (by omega)).2.1
                        · exact hdisjC a (by omega) b (by omega) hab
              · have hi_eq : i.toNat = n.toNat := by
                  simp only [LeanQbe.T.Arg.val_var] at hc
                  have hlt := Nat.not_lt.mp (of_decide_eq_false hc); omega
                have hmC' := unfocus_defrag hmC
                dsimp only at hmC'
                let sC : FullState :=
                  { s with core := { s.core with wvec := wvecC, wstk := wstkC },
                           scratch := { s.scratch with wsort := wsort2 } }
                have hwvC' : sC.LengthsOk c :=
                  ⟨{ hcl with wvec_len := hwvC, wstk_len_arr := hwsC },
                   { hsl with wsort_len := hws2 }⟩
                open LeanQbe.T.C0HeadStep FullArenaTactics FullIngestTactics in c0_hsteps_nogrp
                rw [hi_eq] at hdoneC hdisjC
                have hfin := m4Defrag_finalize hlay hcov2 hp1 hszC hzeroC hdoneC hdisjC
                refine hQ wvecC wstkC p.toNat wsort2 _
                  ⟨{ hcl with wvec_len := hwvC, wstk_len_arr := hwsC,
                              wlen_le := by dsimp only; omega }, { hsl with wsort_len := hws2 }⟩
                  hfin.1 (fun _ => hp1) hfin.2 hm
          · intro J4 hJ4
            clear hQ hlen hcl hsl hwsl hwvl hwle hwsrt_l hwlen_gt1 hwsl_pos
            m4_wp_lets
            simp only [LeanQbe.T.wp_jnz, LeanQbe.T.Arg.val_var]
            refine ⟨fun hso_t => ?_, fun hns => ?_⟩
            · m4_wp_jump
              exact hJ4 _ _ ⟨wsort1, hws1, hcov1, (hsort1 hso_t).1, hm1⟩
            · m4_wp_lets
              try rw [LeanQbe.T.wp_jnz]
              refine ⟨fun hgt1 => ?_, fun hle1 => ?_⟩
              · have hn_gt1 : 1 < n.toNat := by
                  simp only [LeanQbe.T.Arg.val_var] at hgt1
                  exact of_decide_eq_true hgt1
                let key := m4WvecOff wvec1
                have hkey_eq : ∀ l < 2 * s.core.cur_vars,
                    0 < fullWatchSize s l → key l = fullWatchOff s l := fun l hl hp => by
                  unfold key m4WvecOff fullWatchOff fullWatchOffCore; rw [hoff1 l hl hp]
                have hmv_ws : 2 * s.core.cur_vars ≤ wsort1.length := by m4_omega
                have hwvec_lt : 2 * (2 * s.core.cur_vars) ≤ wvec1.length := by m4_omega
                have hsrt_of_key : ∀ ws2 : List (BitVec 32), ws2.length = 2 * c.max_vars →
                    M4WsCovers ws2 n.toNat (2 * s.core.cur_vars) (fullWatchSize s) →
                    M4Sorted key ws2 0 n.toNat →
                    M4Sorted (fullWatchOff s) ws2 0 n.toNat := by
                  intro ws2 _ hcv2 hsrt i j hi hij hj
                  rw [← hkey_eq _ (hcv2.1 i (by m4_omega)).1 (hcv2.1 i (by m4_omega)).2,
                    ← hkey_eq _ (hcv2.1 j hj).1 (hcv2.1 j hj).2]
                  exact hsrt i j hi hij hj
                refine wp_join_group
                  (fun _ m4 => ∃ wsort2 : List (BitVec 32), wsort2.length = 2 * c.max_vars ∧
                    (wsort2.take n.toNat).Perm (wsort1.take n.toNat) ∧
                    M4Sorted key wsort2 0 n.toNat ∧
                    DefragMem c s wvec1 wsort2 s.core.wstk R m4)
                  ?_ ?_
                · rintro _ _ m4 ⟨wsort2, hws2, hpm2, hsrt2, hm4⟩
                  m4_wp_lets
                  m4_wp_jump
                  have hcv2 := m4WsCovers_of_perm_take hcov1 (by m4_omega) (by m4_omega) hpm2
                  exact hJ4 _ _ ⟨wsort2, hws2, hcv2, hsrt_of_key wsort2 hws2 hcv2 hsrt2, hm4⟩
                · intro J7 hJ7
                  clear hsz1 hoff1 hzero1 hsort1 hn_pos J4 hJ4 hns hgt1 hkey_eq hsrt_of_key
                  m4_wp_lets
                  simp only [LeanQbe.T.wp_jnz, LeanQbe.T.Arg.val_var]
                  refine ⟨fun hdbl => ?_, fun hno_dbl => ?_⟩
                  · have h2n_le : 2 * n.toNat ≤ 2 * s.core.cur_vars := by
                      have := of_decide_eq_true hdbl
                      rw [BitVec.toNat_sub, hnlits] at this; m4_omega
                    clear hdbl
                    change wp Γ Q X (m4MergeSortExpr c.pWvec c.pWsort n J7) m1
                    exact m4_mergesort_wp hmx hcv_le hn_le hn_gt1 h2n_le hwv1 hws1
                      hwvec_lt hcov1 hm1 hJ7
                  · have h2n_gt : 2 * s.core.cur_vars < 2 * n.toNat := by
                      unfold BitVec.ule at hno_dbl
                      have := Nat.not_le.mp (of_decide_eq_false hno_dbl)
                      rw [BitVec.toNat_sub, hnlits] at this; m4_omega
                    clear hno_dbl
                    m4_wp_lets
                    refine wp_loop_inv
                      (fun (st, ()) mB => st.toNat ≤ n.toNat ∧ ∃ wsB : List (BitVec 32),
                        wsB.length = 2 * c.max_vars ∧
                        wsB.Perm wsort1 ∧ (∀ p, n.toNat ≤ p → wsB[p]? = wsort1[p]?) ∧
                        (∀ i < n.toNat, m4WsVal wsB i < 2 * s.core.cur_vars) ∧
                        FullWsortMaxHeap wvec1 wsB st.toNat n.toNat ∧
                        DefragMem c s wvec1 wsB s.core.wstk R mB)
                      (fun (st, ()) _ => st.toNat) (fun JB hLoopB => ?_) ?_
                    · m4_wp_lets; m4_wp_jump
                      refine hLoopB _ _ ⟨by rw [m4_bv64_shr1]; m4_omega, wsort1, hws1,
                        List.Perm.refl _, fun _ _ => rfl, fun i hi => (hcov1.1 i hi).1,
                        fun p hp1 hp2 => by
                          rw [m4_bv64_shr1] at hp1
                          exact ⟨fun _ => by m4_omega, fun _ => by m4_omega⟩, hm1⟩
                    · rintro JB ⟨st, ⟨⟩⟩ mB
                        ⟨hst_le, wsB, hwsB, hpmB, hsufB, hbdB, hmaxB, hmB⟩ hLoopB
                      m4_wp_lets
                      simp only [LeanQbe.T.wp_jnz, LeanQbe.T.Arg.val_var]
                      refine ⟨fun hst_pos_c => ?_, fun hst0_c => ?_⟩
                      · have hst_pos : 0 < st.toNat := of_decide_eq_true hst_pos_c
                        have hstm1 : (st - (1 : BitVec 64)).toNat = st.toNat - 1 := by
                          rw [BitVec.toNat_sub,
                            show ((1 : BitVec 64) : BitVec 64).toNat = 1 from rfl]
                          have := st.isLt; m4_omega
                        have hstm1_ws : st.toNat - 1 < wsB.length := by m4_omega
                        have hrl_cv : (wsB[st.toNat - 1]'hstm1_ws).toNat < 2 * s.core.cur_vars := by
                          have := hbdB (st.toNat - 1) (by m4_omega)
                          unfold m4WsVal at this; rwa [List.getElem?_eq_getElem hstm1_ws,
                            Option.getD_some] at this
                        have hrl2_lt : 2 * (wsB[st.toNat - 1]'hstm1_ws).toNat < wvec1.length := by
                          m4_omega
                        m4_wp_lets
                        refine wp_load_sep_at
                          (ptr := c.pWsort + BitVec.ofNat 64 (4 * (st.toNat - 1)))
                          (by simp only [LeanQbe.T.Arg.val_var]
                              rw [m4_ptr_mul4_sub1 c.pWsort st hst_pos])
                          (dsm_load_ws hstm1_ws hmB) ?_
                        m4_wp_lets
                        refine wp_load_sep_at
                          (ptr := c.pWvec + BitVec.ofNat 64
                            (4 * (2 * (wsB[st.toNat - 1]'hstm1_ws).toNat)))
                          (by try simp only [LeanQbe.T.Arg.val_var]; rw [ptr_mul4_eq, m4_zext_shl1])
                          (dsm_load_wvec hrl2_lt hmB) ?_
                        let rlB := wsB[st.toNat - 1]'hstm1_ws
                        have hdoneB : ∀ mD,
                            (∃ wsD : List (BitVec 32), wsD.length = 2 * c.max_vars ∧
                              wsD.Perm wsB ∧ (∀ p, n.toNat ≤ p → wsD[p]? = wsB[p]?) ∧
                              FullWsortMaxHeap wvec1 wsD (st.toNat - 1) n.toNat ∧
                              DefragMem c s wvec1 wsD s.core.wstk R mD) →
                            wp Γ Q X (Expr.jump JB (Arg.var (st - (1 : BitVec 64)), ())) mD := by
                          rintro mD ⟨wsD, hwsD, hpmD, hsufD, hmaxD, hmD⟩
                          m4_wp_lets; m4_wp_jump
                          have htpD := m4Perm_take_of_drop_eq (by rw [hwsD, hwsB]) (by m4_omega)
                            hpmD hsufD
                          refine hLoopB _ _ (by dsimp only; rw [hstm1]; m4_omega)
                            ⟨by rw [hstm1]; m4_omega, wsD, hwsD, hpmD.trans hpmB,
                             fun p hp => (hsufD p hp).trans (hsufB p hp), fun i hi => ?_,
                             by rw [hstm1]; exact hmaxD, hmD⟩
                          have hmem : wsD[i]'(by m4_omega) ∈ wsD.take n.toNat := by
                            have := List.getElem_mem (l := wsD.take n.toNat) (n := i)
                              (by simp [List.length_take]; m4_omega)
                            rwa [List.getElem_take] at this
                          obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp (htpD.mem_iff.mp hmem)
                          simp only [List.length_take] at hj; rw [List.getElem_take] at hget
                          unfold m4WsVal
                          rw [List.getElem?_eq_getElem (by m4_omega), Option.getD_some, ← hget]
                          have := hbdB j (by m4_omega); unfold m4WsVal at this
                          rwa [List.getElem?_eq_getElem (by m4_omega), Option.getD_some] at this
                        m4_sift_inner key, wsB, n, rlB, n.toNat, c.max_vars, wvec1, c, s, R,
                          hdoneB, (st.toNat - 1), n.toNat,
                          (by
                            intro JL hJL
                            m4_wp_lets; m4_wp_jump
                            refine hJL _ _ ⟨by rw [hstm1]; exact le_refl _,
                              by rw [hstm1]; m4_omega, wsB,
                              hwsB, fun _ _ => rfl, hrl_cv, fun i hi _ => by
                                have := hbdB i hi; unfold m4WsVal at this; exact this,
                              ⟨by rw [hstm1, List.set_getElem_self hstm1_ws],
                               by rw [hstm1, List.set_getElem_self hstm1_ws]; exact fun _ _ => rfl,
                               fun p hp1 hp2 hp3 => by
                                 rw [hstm1, List.set_getElem_self hstm1_ws]
                                 exact hmaxB p (by m4_omega) hp2,
                               fun hlt _ => by rw [hstm1] at hlt; m4_omega⟩, hmB⟩)
                      · have hst0 : st.toNat = 0 := by
                          try unfold BitVec.ult at hst0_c
                          have := Nat.not_lt.mp (of_decide_eq_false hst0_c)
                          rw [show ((0 : BitVec 64) : BitVec 64).toNat = 0 from rfl] at this
                          m4_omega
                        rw [hst0] at hmaxB; clear hst0_c hLoopB JB st hst_le hst0
                        m4_wp_lets
                        refine wp_loop_inv
                          (fun (e, ()) mE => e.toNat < n.toNat ∧ ∃ wsE : List (BitVec 32),
                            wsE.length = 2 * c.max_vars ∧
                            wsE.Perm wsort1 ∧ (∀ p, n.toNat ≤ p → wsE[p]? = wsort1[p]?) ∧
                            (∀ i < n.toNat, m4WsVal wsE i < 2 * s.core.cur_vars) ∧
                            FullWsortMaxHeap wvec1 wsE 0 (e.toNat + 1) ∧
                            M4SplitLe key wsE (e.toNat + 1) n.toNat ∧
                            M4Sorted key wsE (e.toNat + 1) n.toNat ∧
                            DefragMem c s wvec1 wsE s.core.wstk R mE)
                          (fun (e, ()) _ => e.toNat) (fun JE hLoopE => ?_) ?_
                        · m4_wp_lets; m4_wp_jump
                          have hnm1 : (n - (1 : BitVec 64)).toNat = n.toNat - 1 := by
                            rw [BitVec.toNat_sub,
                              show ((1 : BitVec 64) : BitVec 64).toNat = 1 from rfl]
                            have := n.isLt; m4_omega
                          refine hLoopE _ _ ⟨by m4_omega, wsB, hwsB, hpmB, hsufB, hbdB,
                            by rw [hnm1, show n.toNat - 1 + 1 = n.toNat by m4_omega]; exact hmaxB,
                            fun _ _ _ _ _ => by m4_omega, fun _ _ _ _ _ => by m4_omega, hmB⟩
                        · rintro JE ⟨e, ⟨⟩⟩ mE
                            ⟨he_lt, wsE, hwsE, hpmE, hsufE, hbdE, hmaxE, hspE, hsrtE, hmE⟩ hLoopE
                          clear hmB wsB hwsB hpmB hsufB hbdB hmaxB
                          m4_wp_lets; simp only [LeanQbe.T.wp_jnz, LeanQbe.T.Arg.val_var]
                          refine ⟨fun he_pos_c => ?_, fun he0_c => ?_⟩
                          · have he_pos : 0 < e.toNat := of_decide_eq_true he_pos_c
                            have he_ws : e.toNat < wsE.length := by m4_omega
                            have h0_ws : 0 < wsE.length := by m4_omega
                            have hem1 : (e - (1 : BitVec 64)).toNat = e.toNat - 1 := by
                              rw [BitVec.toNat_sub,
                                show ((1 : BitVec 64) : BitVec 64).toNat = 1 from rfl]
                              have := e.isLt; m4_omega
                            have hrl_cv : (wsE[e.toNat]'he_ws).toNat < 2 * s.core.cur_vars := by
                              have := hbdE e.toNat he_lt; unfold m4WsVal at this
                              rwa [List.getElem?_eq_getElem he_ws, Option.getD_some] at this
                            have hrl2_lt :
                                2 * (wsE[e.toNat]'he_ws).toNat < wvec1.length := by
                              m4_omega
                            m4_wp_lets
                            refine wp_load_sep_at (ptr := c.pWsort + BitVec.ofNat 64 (4 * e.toNat))
                              (ptr_mul4_eq c.pWsort e) (dsm_load_ws he_ws hmE) ?_
                            m4_wp_lets
                            refine wp_load_sep_at (ptr := c.pWsort + BitVec.ofNat 64 (4 * 0))
                              (by simp) (dsm_load_ws h0_ws hmE) ?_
                            m4_wp_lets
                            refine wp_store_sep_at (ptr := c.pWsort + BitVec.ofNat 64 (4 * e.toNat))
                              (ptr_mul4_eq c.pWsort e)
                              (dsm_store_ws (wsE[0]'h0_ws) he_ws hmE) fun mE1 hmE1 => ?_
                            m4_wp_lets
                            refine wp_load_sep_at
                              (ptr := c.pWvec + BitVec.ofNat 64
                                (4 * (2 * (wsE[e.toNat]'he_ws).toNat)))
                              (by try simp only [LeanQbe.T.Arg.val_var]
                                  rw [ptr_mul4_eq, m4_zext_shl1])
                              (dsm_load_wvec hrl2_lt hmE1) ?_
                            let rlE := wsE[e.toNat]'he_ws
                            let wsE1 := wsE.set e.toNat (wsE[0]'h0_ws)
                            let wsSwap := (wsE.set 0 rlE).set e.toNat (wsE[0]'h0_ws)
                            have hsw_step := m4Wsort_extract_swap hmaxE hspE hsrtE he_pos he_lt
                              (by m4_omega)
                            have hsw_eq : wsE1.set 0 rlE = wsSwap := by
                              apply List.ext_getElem
                              · simp [wsE1, wsSwap]
                              · intro k hk _; simp only [wsE1, List.length_set] at hk
                                by_cases hke : k = e.toNat <;> by_cases hk0 : k = 0 <;>
                                  simp [wsE1, wsSwap, List.getElem_set, hke, hk0] <;>
                                  (try split) <;> first | rfl | m4_omega
                            have hwsSwap_perm : wsSwap.Perm wsE :=
                              m4WsSwap_perm (i := 0) (j := e.toNat) h0_ws he_ws
                            have hwsSwap_suf : ∀ p, e.toNat + 1 ≤ p → wsSwap[p]? = wsE[p]? :=
                              fun p hp => by
                                rw [List.getElem?_set_ne (by m4_omega),
                                  List.getElem?_set_ne (by m4_omega)]
                            have hdoneE : ∀ mD,
                                (∃ wsD : List (BitVec 32), wsD.length = 2 * c.max_vars ∧
                                  wsD.Perm wsSwap ∧
                                  (∀ p, e.toNat ≤ p → wsD[p]? = wsSwap[p]?) ∧
                                  FullWsortMaxHeap wvec1 wsD 0 e.toNat ∧
                                  DefragMem c s wvec1 wsD s.core.wstk R mD) →
                                wp Γ Q X (Expr.jump JE (Arg.var (e - (1 : BitVec 64)), ())) mD := by
                              rintro mD ⟨wsD, hwsD, hpmD, hsufD, hmaxD, hmD⟩
                              m4_wp_lets; m4_wp_jump
                              have ⟨hsp', hsrt'⟩ := m4Wsort_extract_perm_post
                                (by rw [hwsD]; simp [wsSwap, hwsE]) (by m4_omega)
                                (by simp [wsSwap, hwsE]; m4_omega) hpmD hsufD
                                hsw_step.2.1 hsw_step.2.2
                              have htpD := m4Perm_take_of_drop_eq
                                (by rw [hwsD, hwsE]) (by m4_omega) (hpmD.trans hwsSwap_perm)
                                fun p hp => (hsufD p (by m4_omega)).trans (hwsSwap_suf p hp)
                              refine hLoopE _ _ (by dsimp only; rw [hem1]; m4_omega)
                                ⟨by rw [hem1]; m4_omega, wsD, hwsD,
                                 (hpmD.trans hwsSwap_perm).trans hpmE,
                                 fun p hp =>
                                   ((hsufD p (by m4_omega)).trans
                                     (hwsSwap_suf p (by m4_omega))).trans (hsufE p hp),
                                 fun i hi => ?_,
                                 by
                                   rw [hem1, show e.toNat - 1 + 1 = e.toNat by m4_omega]
                                   exact hmaxD,
                                 by
                                   rw [hem1, show e.toNat - 1 + 1 = e.toNat by m4_omega]
                                   exact hsp',
                                 by
                                   rw [hem1, show e.toNat - 1 + 1 = e.toNat by m4_omega]
                                   exact hsrt',
                                 hmD⟩
                              rcases Nat.lt_trichotomy i e.toNat with hie | rfl | hie
                              · have hmem : wsD[i]'(by m4_omega) ∈ wsD.take (e.toNat + 1) := by
                                  have := List.getElem_mem (l := wsD.take (e.toNat + 1)) (n := i)
                                    (by simp [List.length_take]; m4_omega)
                                  rwa [List.getElem_take] at this
                                obtain ⟨j, hj, hget⟩ :=
                                  List.mem_iff_getElem.mp (htpD.mem_iff.mp hmem)
                                simp only [List.length_take] at hj; rw [List.getElem_take] at hget
                                unfold m4WsVal; rw [List.getElem?_eq_getElem (by m4_omega),
                                  Option.getD_some, ← hget]
                                have := hbdE j (by m4_omega); unfold m4WsVal at this
                                rwa [List.getElem?_eq_getElem (by m4_omega),
                                  Option.getD_some] at this
                              · unfold m4WsVal; rw [hsufD e.toNat (le_refl _)]
                                dsimp only [wsSwap]
                                rw [List.getElem?_set_self (by simp [hwsE]; m4_omega),
                                  Option.getD_some]
                                have := hbdE 0 (by m4_omega); unfold m4WsVal at this
                                rwa [List.getElem?_eq_getElem h0_ws, Option.getD_some] at this
                              · unfold m4WsVal
                                rw [hsufD i (by m4_omega), hwsSwap_suf i (by m4_omega)]
                                exact hbdE i hi
                            m4_sift_inner key, wsSwap, e, rlE, n.toNat, c.max_vars, wvec1, c, s, R,
                              hdoneE, 0, e.toNat,
                              (by
                                intro JL hJL
                                m4_wp_lets; m4_wp_jump
                                refine hJL _ _ ⟨Nat.zero_le _, he_pos, wsE1,
                                  by simp [wsE1, hwsE],
                                  fun p hp => by
                                    by_cases hpe : p = e.toNat
                                    · subst hpe; dsimp only [wsE1, wsSwap]
                                      rw [List.getElem?_set_self he_ws, List.getElem?_set_self
                                        (by rw [List.length_set]; exact he_ws)]
                                    · simp [wsE1, wsSwap, List.getElem?_set_ne (Ne.symm hpe),
                                        List.getElem?_set_ne (by m4_omega : 0 ≠ p)],
                                  hrl_cv, fun i hi hne => ?_,
                                  ⟨by
                                     rw [show ((0 : BitVec 64) : BitVec 64).toNat = 0 from rfl,
                                       hsw_eq],
                                   by
                                     rw [show ((0 : BitVec 64) : BitVec 64).toNat = 0 from rfl,
                                       hsw_eq]
                                     exact fun _ _ => rfl,
                                   by
                                     rw [show ((0 : BitVec 64) : BitVec 64).toNat = 0 from rfl,
                                       hsw_eq]
                                     dsimp only [wsSwap, rlE]
                                     exact fun p _ hp2 hp3 =>
                                       hsw_step.1 p (Nat.pos_of_ne_zero hp3) hp2 hp3,
                                   fun h0 => absurd h0 (Nat.lt_irrefl 0)⟩, hmE1⟩
                                by_cases hie : i = e.toNat
                                · subst hie; simp only [wsE1, List.getElem?_set_self he_ws,
                                    Option.getD_some]
                                  have := hbdE 0 (by m4_omega); unfold m4WsVal at this
                                  rwa [List.getElem?_eq_getElem h0_ws, Option.getD_some] at this
                                · simp only [wsE1, List.getElem?_set_ne (Ne.symm hie)]
                                  exact hbdE i hi)
                          · have he0 : e.toNat = 0 := by
                              try unfold BitVec.ult at he0_c
                              have := Nat.not_lt.mp (of_decide_eq_false he0_c)
                              rw [show ((0 : BitVec 64) : BitVec 64).toNat = 0 from rfl] at this
                              m4_omega
                            rw [he0] at hspE hsrtE
                            m4_wp_jump
                            refine hJ7 _ _ ⟨wsE, hwsE,
                              m4Perm_take_of_drop_eq (by rw [hwsE, hws1]) (by m4_omega) hpmE hsufE,
                              fun i j hi hij hj => ?_, hmE⟩
                            rcases Nat.eq_zero_or_pos i with rfl | hip
                            · rcases Nat.eq_zero_or_pos j with rfl | hjp
                              · exact Nat.le_refl _
                              · exact hspE 0 (by m4_omega) j (by m4_omega) hj
                            · exact hsrtE i j (by m4_omega) hij hj
              · have hn1 : n.toNat ≤ 1 := by
                  try unfold BitVec.ult at hle1
                  have := Nat.not_lt.mp (of_decide_eq_false hle1)
                  rw [show ((1 : BitVec 64) : BitVec 64).toNat = 1 from rfl] at this
                  m4_omega
                m4_wp_jump
                refine hJ4 _ _ ⟨wsort1, hws1, hcov1, fun i j _ hij hj => ?_, hm1⟩
                have heq : i = j := by m4_omega
                subst heq; exact Nat.le_refl _

end DefragM4

/-! ## 5. Closed `3`-Row `ModuleOk` Assembly & Concrete `Mem 64` Non-Vacuity -/

def m4InprocHotSpecTable : List SpecEntry :=
  [ ⟨"full_has_ternary_m4", [i64, i32, i32, i32], [.bool], Full.fullHasTernarySpec, true⟩
  , ⟨"full_kitten_init_m4", [i64, i32, i32], [], Full.fullKittenInitSpec, true⟩
  , ⟨"full_wstack_defrag_m4", [i64], [], Full.fullWstackDefragSpec, true⟩
  ]

def m4InprocHotEnv : Env := Env.ofTable m4InprocHotSpecTable

theorem m4InprocHotSpecTable_sigs :
    m4InprocHotSpecTable.map (fun e => (e.name, e.as, e.rs)) =
      m4InprocHot_fns.map (fun f => (f.name, f.as, f.rs)) := rfl

theorem m4InprocHotEnv_noExit :
    ∀ f as bs xs m Q X X',
      m4InprocHotEnv f as bs xs m Q X → m4InprocHotEnv f as bs xs m Q X' :=
  Env.ofTable_noExit fun e he => by
    simp only [m4InprocHotSpecTable, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> rfl

theorem m4InprocHot_allFns_wf : AllFns Fn.Wf m4InprocHotModule.fns :=
  ⟨full_has_ternary_m4_wf, full_kitten_init_m4_wf, full_wstack_defrag_m4_wf, trivial⟩

theorem m4InprocHot_tableImpl :
    TableImpl m4InprocHotEnv m4InprocHotModule.fns m4InprocHotSpecTable :=
  ⟨SpecEntry.Impl.of (full_has_ternary_m4_wp m4InprocHotEnv),
   SpecEntry.Impl.of (full_kitten_init_m4_wp m4InprocHotEnv),
   SpecEntry.Impl.of (full_wstack_defrag_m4_wp m4InprocHotEnv),
   trivial⟩

/-- Closed `3`-row `ModuleOk` witness linking `m4InprocHotModule` to `m4InprocHotEnv`. -/
theorem m4InprocHot_moduleOk : ModuleOk m4InprocHotEnv m4InprocHotModule :=
  Env.ofTable_moduleOk m4InprocHot_acyclic m4InprocHot_allFns_wf m4InprocHot_tableImpl

/-- Concrete `Mem 64` non-vacuity (`XPost := False`) for `full_has_ternary_m4`. -/
theorem nv_m4_has_ternary :
    Func.wp m4InprocHotEnv full_has_ternary_m4_body (nvM4Cfg.hdr, 0#32, 0#32, 0#32, ()) nvM4Mem
      (fun (ok, ()) _ => ok = true → (0#32 : BitVec 32) ≠ 0#32 → False)
      (fun _ _ _ _ => False) :=
  full_has_ternary_m4_wp m4InprocHotEnv _ nvM4Mem _ (fun _ _ _ _ => False)
    ⟨nvM4Cfg, cnfOfClauses [], [], nvM4State, emp, rfl, nvM4State_lengths, nvM4_witness,
     (fun _ h _ => by
       change _ ∈ fullArenaClauseRefsCore nvM4State.core at h
       rw [nvM4_refs_nil] at h; cases h),
     rfl, (by decide), (by rw [sep_emp]; exact nvM4Mem_ok), fun _ _ _ hne => hne rfl⟩

/-- Concrete `Mem 64` non-vacuity (`XPost := False`) for `full_kitten_init_m4`. -/
theorem nv_m4_kitten_init :
    Func.wp m4InprocHotEnv full_kitten_init_m4_body (nvM4Cfg.hdr, 1#32, 0#32, ()) nvM4Mem
      (fun _ _ => True) (fun _ _ _ _ => False) :=
  full_kitten_init_m4_wp m4InprocHotEnv _ nvM4Mem _ (fun _ _ _ _ => False)
    ⟨nvM4Cfg, nvM4State, emp, rfl, nvM4State_lengths, (by rw [sep_emp]; exact nvM4Mem_ok),
     by simp [kMinScratchCap, kMaxV, nvM4Cfg]⟩

/-- Concrete `Mem 64` non-vacuity (`XPost := False`) for `full_wstack_defrag_m4`. -/
theorem nv_m4_wstack_defrag :
    Func.wp m4InprocHotEnv full_wstack_defrag_m4_body (nvM4Cfg.hdr, ()) nvM4Mem
      (fun _ _ => True) (fun _ _ _ _ => False) :=
  full_wstack_defrag_m4_wp m4InprocHotEnv _ nvM4Mem _ (fun _ _ _ _ => False)
    ⟨nvM4Cfg, nvM4State, emp, rfl, nvM4State_lengths, nvM4_layout,
     (by rw [sep_emp]; exact nvM4Mem_ok), fun _ _ _ _ _ _ _ _ _ _ => trivial⟩

end LeanQbe.T.Examples.Kissat.FullM4InprocHot
