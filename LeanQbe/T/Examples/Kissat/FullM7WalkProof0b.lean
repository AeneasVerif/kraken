module

public import LeanQbe.T.Examples.Kissat.FullM7WalkProof0
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import Kraken.Mem
import Kraken.Separation

/-!
# ProbSAT Walk Helper WP Proofs (`collect`, `build_occ`, `pick` — Part 0b)

Parametric `(Γ : Env)` `Func.wp` proofs (`XPost := False`, UNSAT soundness + memory safety only)
for the remaining walk preparation/selection helpers defined in `FullM7Walk`:
- `full_walk_collect_m7` (`full_walk_collect_m7_wp`)
- `full_walk_build_occ_m7` (`full_walk_build_occ_m7_wp`)
- `full_walk_pick_m7` (`full_walk_pick_m7_wp`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7Walk

open Std Std.Sat Std.ExtHashMap LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
  LeanQbe.T.ProofUtil LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
  Kraken.Bedrock2.Test LeanQbe.T.Examples.Kissat.Full
open scoped FullArenaTactics

private theorem m7b_strip_32_64 {P : Prop} (h : P) : 32 ≤ 64 ∧ P := ⟨by decide, h⟩
private theorem m7b_strip_8_32 {P : Prop} (h : P) : 8 ≤ 32 ∧ P := ⟨by decide, h⟩
private theorem m7b_strip_8_64 {P : Prop} (h : P) : 8 ≤ 64 ∧ P := ⟨by decide, h⟩

local macro "m7b_strip" : tactic =>
  `(tactic| first | apply m7b_strip_32_64 | apply m7b_strip_8_32 | apply m7b_strip_8_64)
local macro "m7b_unmdata" : tactic =>
  `(tactic| first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)
local macro "m7b_hsteps_nj" : tactic =>
  `(tactic| (
      (try m7b_unmdata)
      (repeat m7b_strip)
      repeat c0_step))

local macro "m7b_jnz" h:ident : tactic =>
  `(tactic| (
      c0_let_simp
      refine LeanQbe.T.wp_jnz_of (fun $h:ident => ?_) (fun $h:ident => ?_)
      all_goals
        (try simp only [LeanQbe.T.Arg.val_var] at $h:ident)
        c0_cond $h:ident
        try c0_let_simp))

private theorem m7b_zext32 (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat :=
  zext_toNat x (by decide)

private theorem m7b_zext8 (x : BitVec 8) : (x.setWidth 64).toNat = x.toNat :=
  zext_toNat x (by decide)

private theorem m7b_zext32_lt {v cap : Nat} {x : BitVec 32} (hx : x.toNat < v) (hv : v ≤ cap) :
    (x.setWidth 64).toNat < cap := by
  rw [m7b_zext32]; omega

private theorem m7b_bv64_shl1_toNat {x : BitVec 64} (hx : 2 * x.toNat < 2 ^ 64) :
    (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, show 2 ^ 1 = 2 from rfl,
    show x.toNat * 2 = 2 * x.toNat by omega, Nat.mod_eq_of_lt hx]

private theorem m7b_bv64_add1_toNat {x : BitVec 64} (hx : x.toNat + 1 < 2 ^ 64) :
    (x + 1#64).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt hx]

private theorem m7b_ext_refl (s : FullState) : FullExtScratchPres s s := ⟨rfl, rfl⟩

private theorem m7b_ext_trans {s1 s2 s3 : FullState}
    (h12 : FullExtScratchPres s1 s2) (h23 : FullExtScratchPres s2 s3) :
    FullExtScratchPres s1 s3 :=
  ⟨h23.1.trans h12.1, h23.2.trans h12.2⟩

private theorem m7b_ext_scrBuf (s : FullState) (b : List (BitVec 32)) :
    FullExtScratchPres s { s with scratch := { s.scratch with scratch_buf := b } } :=
  m7b_ext_refl s

private theorem m7b_ext_tmk (s : FullState) (b : List (BitVec 32)) :
    FullExtScratchPres s { s with scratch := { s.scratch with tarjan_mark := b } } :=
  m7b_ext_refl s

private theorem m7b_ext_trc (s : FullState) (b : List (BitVec 32)) :
    FullExtScratchPres s { s with scratch := { s.scratch with tarjan_reach := b } } :=
  m7b_ext_refl s

private theorem m7b_ext_ws (s : FullState) (b : List (BitVec 32)) :
    FullExtScratchPres s { s with scratch := { s.scratch with wsort := b } } :=
  m7b_ext_refl s

private theorem m7b_ext_wk1 (s : FullState) (b : List (BitVec 32)) :
    FullExtScratchPres s { s with scratch := { s.scratch with work_stk1 := b } } :=
  m7b_ext_refl s

private theorem m7b_ext_wk2 (s : FullState) (b : List (BitVec 32)) :
    FullExtScratchPres s { s with scratch := { s.scratch with work_stk2 := b } } :=
  m7b_ext_refl s

private theorem m7b_len_scrBuf {c : FullCfg} {s : FullState} {i : Nat} {v : BitVec 32}
    (h : s.LengthsOk c) :
    ({ s with scratch :=
        { s.scratch with scratch_buf := s.scratch.scratch_buf.set i v } }).LengthsOk c :=
  ⟨h.core_ok, { h.scratch_ok with
    scratch_buf_len := by rw [List.length_set, h.scratch_ok.scratch_buf_len] }⟩

private theorem m7b_len_tmk {c : FullCfg} {s : FullState} {i : Nat} {v : BitVec 32}
    (h : s.LengthsOk c) :
    ({ s with scratch :=
        { s.scratch with tarjan_mark := s.scratch.tarjan_mark.set i v } }).LengthsOk c :=
  ⟨h.core_ok, { h.scratch_ok with
    tarjan_mark_len := by rw [List.length_set, h.scratch_ok.tarjan_mark_len] }⟩

private theorem m7b_len_trc {c : FullCfg} {s : FullState} {i : Nat} {v : BitVec 32}
    (h : s.LengthsOk c) :
    ({ s with scratch :=
      { s.scratch with tarjan_reach := s.scratch.tarjan_reach.set i v } }).LengthsOk c :=
  ⟨h.core_ok, { h.scratch_ok with
    tarjan_reach_len := by rw [List.length_set, h.scratch_ok.tarjan_reach_len] }⟩

private theorem m7b_len_ws {c : FullCfg} {s : FullState} {i : Nat} {v : BitVec 32}
    (h : s.LengthsOk c) :
    ({ s with scratch := { s.scratch with wsort := s.scratch.wsort.set i v } }).LengthsOk c :=
  ⟨h.core_ok, { h.scratch_ok with wsort_len := by rw [List.length_set, h.scratch_ok.wsort_len] }⟩

private theorem m7b_len_wk1 {c : FullCfg} {s : FullState} {i : Nat} {v : BitVec 32}
    (h : s.LengthsOk c) :
    ({ s with scratch := { s.scratch with work_stk1 := s.scratch.work_stk1.set i v } }).LengthsOk
      c :=
  ⟨h.core_ok, { h.scratch_ok with
    work_stk1_len := by rw [List.length_set, h.scratch_ok.work_stk1_len] }⟩

private theorem m7b_len_wk2 {c : FullCfg} {s : FullState} {i : Nat} {v : BitVec 32}
    (h : s.LengthsOk c) :
    ({ s with scratch := { s.scratch with work_stk2 := s.scratch.work_stk2.set i v } }).LengthsOk
      c :=
  ⟨h.core_ok, { h.scratch_ok with
    work_stk2_len := by rw [List.length_set, h.scratch_ok.work_stk2_len] }⟩

private theorem m7b_bv64_ofNat_eq {x : Nat} (hx : x < 2 ^ 64) :
    (BitVec.ofNat 64 x).toNat = x := bv64_ofNat_toNat hx

private theorem m7b_bv32_ofNat_eq {x : Nat} (hx : x < 2 ^ 32) :
    (BitVec.ofNat 32 x).toNat = x := bv32_ofNat_toNat hx

private theorem m7b_bv64_32_add_2n {n : BitVec 64} (h : 32 + 2 * n.toNat + 1 < 2 ^ 64) :
    (32#64 + (n <<< (1 : Nat))).toNat = 32 + 2 * n.toNat := by
  rw [BitVec.toNat_add, show (32#64 : BitVec 64).toNat = 32 from rfl,
    m7b_bv64_shl1_toNat (by omega), Nat.mod_eq_of_lt (by omega)]

private theorem m7b_bv64_32_add_2n1 {n : BitVec 64} (h : 32 + 2 * n.toNat + 1 < 2 ^ 64) :
    (32#64 + (n <<< (1 : Nat)) + 1#64).toNat = 32 + 2 * n.toNat + 1 := by
  rw [BitVec.toNat_add, m7b_bv64_32_add_2n h, show (1#64 : BitVec 64).toNat = 1 from rfl,
    Nat.mod_eq_of_lt h]

private theorem m7b_state_abs {c : FullCfg} {R : Mem 64 → Prop} {m : Mem 64}
    (s : FullState) {s_new : FullState} (hm : (FullMem c s_new ⋆ R) m)
    (hc : PreservesCoreSlice FullState.core s s_new)
    (hl : s_new.LengthsOk c) (he : FullExtScratchPres s s_new) :
    ∃ st : FullState, PreservesCoreSlice FullState.core s st ∧
      st.LengthsOk c ∧ FullExtScratchPres s st ∧ (FullMem c st ⋆ R) m :=
  ⟨s_new, hc, hl, he, hm⟩

/-- `full_walk_collect_m7` satisfies `m7CollectSpec`. -/
theorem full_walk_collect_m7_wp (Γ : Env)
    (hArenaNext : ∀ args m Q X, fullArenaNextSpec args m Q X →
      Γ "full_arena_next" [i64, i32] [i32] args m Q X) :
    ∀ a m Q X, m7CollectSpec a m Q X →
      Func.wp Γ full_walk_collect_m7_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hspec
  rw [m7CollectSpec_eq] at hspec
  dsimp only [SafetySlice.spec, fullSafetySlice] at hspec
  rcases hspec with ⟨c, s, R, rfl, hlen, hm, hQ⟩
  have hmax := c.hmaxv; have haca := c.harena; have hwc := c.hwcap; have hscr := c.hscr
  unfold dimacsBound at hmax haca hwc hscr
  have hcv_le := hlen.core_ok.cur_vars_le
  have harl := hlen.core_ok.arena_len_arr
  have hale := hlen.core_ok.arena_len_le
  have hvl := hlen.core_ok.vals_len
  have hwvl := hlen.core_ok.wvec_len
  have hwsl := hlen.core_ok.wstk_len_arr
  have hwll := hlen.core_ok.wlen_le
  have hsbl := hlen.scratch_ok.scratch_buf_len
  c0_hsplit
  · c0_hsteps; exact hQ (0#64, ()) s m rfl hlen (m7b_ext_refl s) hm
  c0_hsplit
  · c0_hsteps; exact hQ (0#64, ()) s m rfl hlen (m7b_ext_refl s) hm
  c0_hsplit
  · c0_hsteps; exact hQ (0#64, ()) s m rfl hlen (m7b_ext_refl s) hm
  have hcv_pos : 0 < s.core.cur_vars :=
    Nat.pos_of_ne_zero fun h0 => by
      have hne : ¬ BitVec.ofNat 64 s.core.cur_vars = 0 := by assumption
      exact hne (by rw [h0]; rfl)
  have hcv_ok : s.core.cur_vars ≤ c.max_vars := by
    have h1 : ¬ c.max_vars % 2 ^ 64 < s.core.cur_vars % 2 ^ 64 := by assumption
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h1; omega
  have hcap64 : 64 ≤ c.scratch_cap := by
    have h1 : ¬ c.scratch_cap % 2 ^ 64 < (64#64 : BitVec 64).toNat := by assumption
    rw [show (64#64 : BitVec 64).toNat = 64 from rfl, Nat.mod_eq_of_lt (by omega)] at h1; omega
  have h2cv_eq : ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat = 2 * s.core.cur_vars := by
    rw [m7b_bv64_shl1_toNat (by rw [m7b_bv64_ofNat_eq (by omega)]; omega),
      m7b_bv64_ofNat_eq (by omega)]
  c0_hsteps_nogrp
  -- Loop 1: scan `l < 2 * cur_vars` for binary clauses
  refine wp_loop_safety_slice_pure (fullSafetySlice c) s R
    (fun s1 (n, tot, ch, l, ()) =>
      n.toNat ≤ c.scratch_cap ∧ tot.toNat ≤ c.scratch_cap ∧
      5 * n.toNat + 32 + tot.toNat ≤ c.scratch_cap ∧
      l.toNat ≤ 2 * s.core.cur_vars ∧ FullExtScratchPres s s1)
    (fun (_, _, _, l, ()) => 2 * s.core.cur_vars - l.toNat)
    (fun J0 hJ0 => by
      c0_hsteps
      exact hJ0 s (0#64, 0#64, false, 0#64, ()) m hm rfl hlen
        ⟨Nat.zero_le _, Nat.zero_le _, by simp; omega, Nat.zero_le _, m7b_ext_refl s⟩)
    (fun J0 s1 (n, tot, ch, l, ()) m1 hcore1 hs1 ⟨hn1, htot1, hcap1, hl1, hpres1⟩ hm1 hJ0 => ?_)
  dsimp only [fullSafetySlice] at hs1 hm1
  have hceq1 : s1.core = s.core := hcore1
  refine wp_join_group (ts := []) (fun () m2 => m2 = m1)
    (fun _ _ m2 hm2 => ?_) (fun J1 hJ1 => ?_)
  · subst m2
    clear J0 hJ0 hl1
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64, i64, .bool, i64])
      (fun (n2, tot2, _ch2, _p2, ()) m2 => ∃ s2 : FullState,
        PreservesCoreSlice FullState.core s s2 ∧ s2.LengthsOk c ∧
        FullExtScratchPres s s2 ∧ (FullMem c s2 ⋆ R) m2)
      (fun _ ⟨n2, tot2, _ch2, _p2, ⟨⟩⟩ m2 ⟨s2, hcore2, hs2, hpres2, hm2⟩ => by
        c0_hsteps
        exact hQ _ s2 m2 hcore2 hs2 hpres2 hm2)
      (fun J2 hJ2 => ?_)
    -- Loop 2: arena scan for large (`>= 3`) clauses
    refine wp_loop_safety_slice_pure (fullSafetySlice c) s1 R
      (fun s2 (n2, tot2, ch2, p, ()) =>
        p.toNat ≤ s.core.arena_len ∧ n2.toNat ≤ c.scratch_cap ∧ tot2.toNat ≤ c.scratch_cap ∧
        5 * n2.toNat + 32 + tot2.toNat ≤ c.scratch_cap ∧ FullExtScratchPres s s2)
      (fun (_, _, _, p, ()) => s.core.arena_len - p.toNat)
      (fun J3 hJ3 => by
        c0_hsteps
        exact hJ3 s1 (n, tot, ch, 0#64, ()) m1 hm1 rfl hs1
          ⟨Nat.zero_le _, hn1, htot1, hcap1, hpres1⟩)
      (fun J3 s2 (n2, tot2, ch2, p, ()) m2 hcore2 hs2
          ⟨hp2, hn2, htot2, hcap2, hpres2⟩ hm2 hJ3 => ?_)
    dsimp only [fullSafetySlice] at hs2 hm2
    have hceq2 : s2.core = s.core := Eq.trans hcore2 hceq1
    c0_hsplit
    · -- `p + 3 <= arena_len`
      c0_hsplit
      · -- `ch2 == true`
        c0_hsteps; exact hJ2 (n2, tot2, ch2, p, ()) m2 ⟨s2, hceq2, hs2, hpres2, hm2⟩
      have hp3_le : p.toNat + 3 ≤ s.core.arena_len := by
        rename_i hcond
        simp only [show (3 : BitVec 64).toNat = 3 from rfl] at hcond
        rw [Nat.mod_eq_of_lt (by omega : p.toNat + 3 < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : s.core.arena_len < 2 ^ 64)] at hcond
        exact hcond
      have hp_ar : p.toNat < s2.core.arena.length := by rw [hceq2, harl]; omega
      have hp2_ar : (p + 2#64).toNat < s2.core.arena.length := by
        rw [BitVec.toNat_add, show (2#64 : BitVec 64).toNat = 2 from rfl,
          Nat.mod_eq_of_lt (by omega), hceq2, harl]; omega
      c0_hsteps_nogrp
      let hdr2 := s2.core.arena[p.toNat]'hp_ar
      let sz2 := s2.core.arena[(p + 2#64).toNat]'hp2_ar
      refine wp_join_group (ts := [i64, i64, .bool])
        (fun (n3, tot3, ch3, ()) m3 => ∃ s3 : FullState,
          PreservesCoreSlice FullState.core s2 s3 ∧ s3.LengthsOk c ∧
          n3.toNat ≤ c.scratch_cap ∧ tot3.toNat ≤ c.scratch_cap ∧
          5 * n3.toNat + 32 + tot3.toNat ≤ c.scratch_cap ∧ FullExtScratchPres s s3 ∧
          (FullMem c s3 ⋆ R) m3)
        (fun _ ⟨n3, tot3, ch3, ⟨⟩⟩ m3 ⟨s3, hcore3, hs3, hn3, htot3, hcap3, hpres3, hm3⟩ => by
          have hceq3 : s3.core = s.core := Eq.trans hcore3 hceq2
          c0_hsteps_nogrp
          c0_call hArenaNext
          refine ⟨c, s3, R, rfl, hs3, hm3, ?_⟩
          dsimp only
          have hp32_eq : (p.setWidth 32).toNat = p.toNat := by
            rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
          have hnb := fullArenaNextOff_bounds (ar := s.core.arena) (alen := s.core.arena_len)
            (cref := p.toNat) hp3_le
          have hnxt_nat : (BitVec.ofNat 32 (fullArenaNextOff s3.core.arena s3.core.arena_len
              (p.setWidth 32).toNat)).toNat =
              fullArenaNextOff s.core.arena s.core.arena_len p.toNat := by
            rw [hceq3, hp32_eq, m7b_bv32_ofNat_eq (by omega)]
          c0_hsplit
          · c0_hsteps
            exact hJ2 (n3, tot3, ch3, p, ()) m3 ⟨s3, hceq3, hs3, hpres3, hm3⟩
          · have hgt : p.toNat < fullArenaNextOff s.core.arena s.core.arena_len p.toNat := by
              rw [hceq3, Nat.mod_eq_of_lt (by omega : p.toNat < 2 ^ 32),
                Nat.mod_eq_of_lt (by omega :
                  fullArenaNextOff s.core.arena s.core.arena_len p.toNat < 2 ^ 32)] at hc
              omega
            c0_hsteps
            exact hJ3 s3 (n3, tot3, ch3, _, ()) m3 hm3
              (by dsimp only; rw [m7b_zext32, hnxt_nat]; omega) hcore3 hs3
              ⟨by rw [m7b_zext32, hnxt_nat]; exact hnb.2, hn3, htot3, hcap3, hpres3⟩)
        (fun J4 hJ4 => ?_)
      -- Check `!garb && !red && sz >= 3 && sz <= arena_len && p + 3 + sz <= arena_len`
      c0_hsplit
      · c0_hsplit
        · c0_hsplit
          · have hsz_le_al : sz2.toNat ≤ s.core.arena_len := by
              rw [Nat.mod_eq_of_lt (by omega : s.core.arena_len < 2 ^ 64)] at hc
              dsimp only [sz2]; simp only [BitVec.toNat_add]
              exact hc
            c0_hsplit
            · have hp3sz_le : p.toNat + 3 + sz2.toNat ≤ s.core.arena_len := by
                dsimp only [sz2]; simp only [BitVec.toNat_add]
                have hsum_64 : ∀ x : BitVec 32, (p.toNat + 3 + x.toNat) % 2 ^ 64 =
                    p.toNat + 3 + x.toNat := fun x =>
                  Nat.mod_eq_of_lt (by have := x.isLt; omega)
                have h3 : (3 : BitVec 64).toNat = 3 := rfl
                rw [Nat.mod_eq_of_lt (by omega : s.core.arena_len < 2 ^ 64)] at hc
                simp only [h3, hsum_64] at hc
                exact hc
              c0_hsteps_nogrp
              -- Read-only scan loop `J5..5` (`wp_loop_break_group`)
              refine wp_loop_break_group
                (fun (_rsat, unass, _k, ()) ma => ma = m2)
                (fun rem (unass, k, ()) ma =>
                  ma = m2 ∧ k.toNat ≤ sz2.toNat ∧ rem = sz2.toNat - k.toNat)
                ?_ ?_ ?_
              · rintro _ ⟨rsat, unass, _k, ⟨⟩⟩ ma hma
                subst ma
                refine wp_join_group (ts := [i64, i64, .bool])
                  (fun (n3, tot3, ch3, ()) m3 => ∃ s3 : FullState,
                    PreservesCoreSlice FullState.core s2 s3 ∧ s3.LengthsOk c ∧
                    n3.toNat ≤ c.scratch_cap ∧ tot3.toNat ≤ c.scratch_cap ∧
                    5 * n3.toNat + 32 + tot3.toNat ≤ c.scratch_cap ∧ FullExtScratchPres s s3 ∧
                    (FullMem c s3 ⋆ R) m3)
                  (fun _ ⟨n3, tot3, ch3, ⟨⟩⟩ m3
                      ⟨s3, hcore3, hs3, hn3, htot3, hcap3, hpres3, hm3⟩ => by
                    c0_hsteps; exact hJ4 (n3, tot3, ch3, ()) m3
                      ⟨s3, hcore3, hs3, hn3, htot3, hcap3, hpres3, hm3⟩)
                  (fun J6 hJ6 => ?_)
                c0_hsplit
                · c0_hsteps
                  exact hJ6 (n2, tot2, ch2, ()) m2 ⟨s2, rfl, hs2, hn2, htot2, hcap2, hpres2, hm2⟩
                c0_hsplit
                · refine wp_join_group (ts := [i64, i64, .bool])
                    (fun (n3, tot3, ch3, ()) m3 => ∃ s3 : FullState,
                      PreservesCoreSlice FullState.core s2 s3 ∧ s3.LengthsOk c ∧
                      n3.toNat ≤ c.scratch_cap ∧ tot3.toNat ≤ c.scratch_cap ∧
                      5 * n3.toNat + 32 + tot3.toNat ≤ c.scratch_cap ∧ FullExtScratchPres s s3 ∧
                      (FullMem c s3 ⋆ R) m3)
                    (fun _ ⟨n3, tot3, ch3, ⟨⟩⟩ m3
                        ⟨s3, hcore3, hs3, hn3, htot3, hcap3, hpres3, hm3⟩ => by
                      c0_hsteps; exact hJ6 (n3, tot3, ch3, ()) m3
                        ⟨s3, hcore3, hs3, hn3, htot3, hcap3, hpres3, hm3⟩)
                    (fun J7 hJ7 => ?_)
                  c0_hsplit
                  · c0_hsteps; exact hJ7 (n2, tot2, true, ()) m2
                      ⟨s2, rfl, hs2, hn2, htot2, hcap2, hpres2, hm2⟩
                  have hsz_raw : s2.core.arena[(p.toNat + BitVec.toNat (2 : BitVec 64)) %
                      2 ^ 64].toNat = sz2.toNat := by
                    dsimp only [sz2]; simp only [BitVec.toNat_add]
                    rfl
                  have hsz_cap : sz2.toNat ≤ c.scratch_cap := by
                    rw [hsz_raw] at hc; omega
                  c0_hsplit
                  · c0_hsteps; exact hJ7 (n2, tot2, true, ()) m2
                      ⟨s2, rfl, hs2, hn2, htot2, hcap2, hpres2, hm2⟩
                  have hn2p1 : (n2 + 1#64).toNat = n2.toNat + 1 := m7b_bv64_add1_toNat (by omega)
                  have hn2p1_le : n2.toNat + 1 ≤ c.scratch_cap := by
                    have h1 : (1 : BitVec 64).toNat = 1 := rfl
                    rw [h1, Nat.mod_eq_of_lt (by omega : c.scratch_cap < 2 ^ 64),
                      Nat.mod_eq_of_lt (by omega : n2.toNat + 1 < 2 ^ 64)] at hc; omega
                  c0_hsplit
                  · c0_hsteps; exact hJ7 (n2, tot2, true, ()) m2
                      ⟨s2, rfl, hs2, hn2, htot2, hcap2, hpres2, hm2⟩
                  have htot_p : (tot2 + sz2.setWidth 64).toNat = tot2.toNat + sz2.toNat := by
                    rw [BitVec.toNat_add, m7b_zext32, Nat.mod_eq_of_lt (by omega)]
                  have htot_le : tot2.toNat + sz2.toNat ≤ c.scratch_cap := by
                    rw [hsz_raw, Nat.mod_eq_of_lt (by omega : tot2.toNat + sz2.toNat < 2 ^ 64)]
                      at hc
                    omega
                  c0_hsplit
                  · c0_hsteps; exact hJ7 (n2, tot2, true, ()) m2
                      ⟨s2, rfl, hs2, hn2, htot2, hcap2, hpres2, hm2⟩
                  have hcap_new : 5 * (n2.toNat + 1) + 32 + (tot2.toNat + sz2.toNat) ≤
                      c.scratch_cap := by
                    try rw [show (1 : BitVec 64).toNat = 1 from rfl] at hc
                    try rw [show (5 : BitVec 64).toNat = 5 from rfl] at hc
                    try rw [show (32 : BitVec 64).toNat = 32 from rfl] at hc
                    rw [hsz_raw] at hc
                    try rw [Nat.mod_eq_of_lt (by omega : n2.toNat + 1 < 2 ^ 64)] at hc
                    try rw [Nat.mod_eq_of_lt (by omega : 5 * (n2.toNat + 1) < 2 ^ 64)] at hc
                    try rw [Nat.mod_eq_of_lt (by omega : 32 + 5 * (n2.toNat + 1) < 2 ^ 64)] at hc
                    try rw [Nat.mod_eq_of_lt (by omega :
                      32 + 5 * (n2.toNat + 1) + tot2.toNat < 2 ^ 64)] at hc
                    try rw [Nat.mod_eq_of_lt (by omega :
                      32 + 5 * (n2.toNat + 1) + tot2.toNat + sz2.toNat < 2 ^ 64)] at hc
                    omega
                  have hsbl2 := hs2.scratch_ok.scratch_buf_len
                  have hi0_eq := m7b_bv64_32_add_2n (n := n2) (by omega)
                  have hi1_eq := m7b_bv64_32_add_2n1 (n := n2) (by omega)
                  have hi0_lt : (32#64 + (n2 <<< (1 : Nat))).toNat <
                      s2.scratch.scratch_buf.length := by rw [hi0_eq, hsbl2]; omega
                  have hi1_lt : (32#64 + (n2 <<< (1 : Nat)) + 1#64).toNat <
                      (s2.scratch.scratch_buf.set (32#64 + (n2 <<< (1 : Nat))).toNat
                        (p.setWidth 32)).length := by
                    rw [List.length_set, hi1_eq, hsbl2]; omega
                  c0_hsteps
                  exact hJ7 (n2 + 1#64, tot2 + sz2.setWidth 64, ch2, ()) _
                    ⟨{ s2 with scratch := { s2.scratch with
                        scratch_buf := (s2.scratch.scratch_buf.set
                          (32#64 + (n2 <<< (1 : Nat))).toNat (p.setWidth 32)).set
                          (32#64 + (n2 <<< (1 : Nat)) + 1#64).toNat 0#32 } },
                      rfl, m7b_len_scrBuf (m7b_len_scrBuf hs2), by rw [hn2p1]; exact hn2p1_le,
                      by rw [htot_p]; exact htot_le,
                      by rw [hn2p1, htot_p]; exact hcap_new, ⟨hpres2.1, hpres2.2⟩, hm⟩
                · c0_hsteps
                  exact hJ6 (n2, tot2, ch2, ()) m2 ⟨s2, rfl, hs2, hn2, htot2, hcap2, hpres2, hm2⟩
              · rintro B _ rem ⟨unass, k, ⟨⟩⟩ ma hB ih ⟨hma, hkle, rfl⟩
                subst ma
                c0_hsplit
                · have hk_lt : k.toNat < sz2.toNat := by assumption
                  have hp3k : (p + 3#64 + k.setWidth 64).toNat = p.toNat + 3 + k.toNat := by
                    rw [BitVec.toNat_add, BitVec.toNat_add, m7b_zext32,
                      show (3#64 : BitVec 64).toNat = 3 from rfl,
                      Nat.mod_eq_of_lt (by omega : p.toNat + 3 < 2 ^ 64),
                      Nat.mod_eq_of_lt (by omega)]
                  have hp3k_ar : (p + 3#64 + k.setWidth 64).toNat < s2.core.arena.length := by
                    rw [hp3k, hceq2, harl]; omega
                  c0_hsteps_nogrp
                  refine wp_join_group (ts := [.bool, .bool])
                    (fun (brk, ua', ()) ma' => ma' = m2)
                    (fun _ ⟨brk, ua', ⟨⟩⟩ ma' hma' => by
                      subst ma'
                      have hk1 : (k + 1#32).toNat = k.toNat + 1 := by
                        rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
                          Nat.mod_eq_of_lt (by omega)]
                      c0_hsteps
                      exact ih (sz2.toNat - (k + 1#32).toNat) (ua', k + 1#32, ()) m2
                        (by rw [hk1]; omega) ⟨rfl, by rw [hk1]; omega, rfl⟩)
                    (fun J7 hJ7 => ?_)
                  c0_hsplit
                  · have hp3k_raw : (s2.core.arena[(p.toNat + BitVec.toNat (3 : BitVec 64) +
                        k.toNat) % 2 ^ 64]'(by
                          rw [show BitVec.toNat (3 : BitVec 64) = 3 from rfl,
                            Nat.mod_eq_of_lt (by omega : p.toNat + 3 + k.toNat < 2 ^ 64),
                            hceq2, harl]; omega)).toNat =
                        (s2.core.arena[(p + 3#64 + k.setWidth 64).toNat]'hp3k_ar).toNat := by
                      congr 2
                      rw [hp3k, show BitVec.toNat (3 : BitVec 64) = 3 from rfl,
                        Nat.mod_eq_of_lt (by omega : p.toNat + 3 + k.toNat < 2 ^ 64)]
                    have hlit_v :
                        ((s2.core.arena[(p + 3#64 + k.setWidth 64).toNat]'hp3k_ar).setWidth
                          64).toNat < s2.core.vals.length := by
                      rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64),
                        Nat.mod_eq_of_lt (by omega : 2 * s.core.cur_vars < 2 ^ 64)] at hc
                      have hvl2 : s2.core.vals.length = 2 * c.max_vars := by rw [hceq2, hvl]
                      rw [m7b_zext32, ← hp3k_raw, hvl2]
                      exact Nat.lt_of_lt_of_le hc (by omega)
                    c0_hsplit
                    · c0_hsteps; exact hB (true, unass, k, ()) m2 rfl
                    · c0_hsteps <;>
                        first
                        | exact hJ7 (false, true, ()) m2 rfl
                        | exact hJ7 (false, unass, ()) m2 rfl
                  · c0_hsteps; exact hJ7 (false, unass, ()) m2 rfl
                · c0_hsteps; exact hB (false, unass, k, ()) m2 rfl
              · intro _ _ _ hL; c0_hsteps
                exact hL sz2.toNat (false, 0#32, ()) m2
                  ⟨rfl, Nat.zero_le _, (Nat.sub_zero _).symm⟩
            · c0_hsteps; exact hJ4 (n2, tot2, ch2, ()) m2
                ⟨s2, rfl, hs2, hn2, htot2, hcap2, hpres2, hm2⟩
          · c0_hsteps; exact hJ4 (n2, tot2, ch2, ()) m2
              ⟨s2, rfl, hs2, hn2, htot2, hcap2, hpres2, hm2⟩
        · c0_hsteps; exact hJ4 (n2, tot2, ch2, ()) m2
            ⟨s2, rfl, hs2, hn2, htot2, hcap2, hpres2, hm2⟩
      · c0_hsteps; exact hJ4 (n2, tot2, ch2, ()) m2
          ⟨s2, rfl, hs2, hn2, htot2, hcap2, hpres2, hm2⟩
    · c0_hsteps; exact hJ2 (n2, tot2, ch2, p, ()) m2 ⟨s2, hceq2, hs2, hpres2, hm2⟩
  · -- Loop 1 body (`l < 2 * cur_vars`)
    c0_hsplit
    · have hl_lt : l.toNat < 2 * s.core.cur_vars := by
        try rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc
        try rw [Nat.mod_eq_of_lt (by omega : 2 * s.core.cur_vars < 2 ^ 64)] at hc
        exact hc
      c0_hsplit
      · c0_hsteps; exact hJ1 () m1 rfl
      have hl1_eq : (l + 1#64).toNat = l.toNat + 1 := m7b_bv64_add1_toNat (by omega)
      refine wp_join_group (ts := [i64, i64, .bool])
        (fun (n2, tot2, ch2, ()) m2 => ∃ s2 : FullState,
          PreservesCoreSlice FullState.core s1 s2 ∧ s2.LengthsOk c ∧
          n2.toNat ≤ c.scratch_cap ∧ tot2.toNat ≤ c.scratch_cap ∧
          5 * n2.toNat + 32 + tot2.toNat ≤ c.scratch_cap ∧ FullExtScratchPres s s2 ∧
          (FullMem c s2 ⋆ R) m2)
        (fun _ ⟨n2, tot2, ch2, ⟨⟩⟩ m2 ⟨s2, hcore2, hs2, hn2, htot2, hcap2, hpres2, hm2⟩ => by
          c0_hsteps
          exact hJ0 s2 (n2, tot2, ch2, l + 1#64, ()) m2 hm2 (by dsimp only; omega)
            hcore2 hs2 ⟨hn2, htot2, hcap2, by omega, hpres2⟩)
        (fun J2 hJ2 => ?_)
      have hl_v : l.toNat < s1.core.vals.length := by rw [hceq1, hvl]; omega
      c0_hsplit
      · have h2l : (l <<< (1 : Nat)).toNat = 2 * l.toNat := m7b_bv64_shl1_toNat (by omega)
        have h2l_wv : (l <<< (1 : Nat)).toNat < s1.core.wvec.length := by
          rw [h2l, hceq1, hwvl]; omega
        have h2l1_eq : ((l <<< (1 : Nat)) + 1#64).toNat = 2 * l.toNat + 1 := by
          rw [BitVec.toNat_add, h2l, show (1#64 : BitVec 64).toNat = 1 from rfl,
            Nat.mod_eq_of_lt (by omega)]
        have h2l1_wv : ((l <<< (1 : Nat)) + 1#64).toNat < s1.core.wvec.length := by
          rw [h2l1_eq, hceq1, hwvl]; omega
        c0_hsteps_nogrp
        let off := (s1.core.wvec[(l <<< (1 : Nat)).toNat]'h2l_wv).setWidth 64
        let len := (s1.core.wvec[((l <<< (1 : Nat)) + 1#64).toNat]'h2l1_wv).setWidth 64
        have hoff_raw : (s1.core.wvec[2 * l.toNat % 2 ^ 64]'(by
            rw [Nat.mod_eq_of_lt (by omega : 2 * l.toNat < 2 ^ 64), hceq1, hwvl]
            omega)).toNat = off.toNat := by
          dsimp only [off]; rw [m7b_zext32]; congr 2
          try rw [h2l]
          try rw [Nat.mod_eq_of_lt (by omega : 2 * l.toNat < 2 ^ 64)]
        have hlen_raw : (s1.core.wvec[(2 * l.toNat +
            BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
              rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl,
                Nat.mod_eq_of_lt (by omega : 2 * l.toNat + 1 < 2 ^ 64), hceq1, hwvl]
              omega)).toNat = len.toNat := by
          dsimp only [len]; rw [m7b_zext32]; congr 2
          try rw [h2l1_eq]
          try rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]
          try rw [Nat.mod_eq_of_lt (by omega : 2 * l.toNat + 1 < 2 ^ 64)]
        refine wp_join_group (ts := [i64, i64, .bool])
          (fun (n2, tot2, ch2, ()) m2 => ∃ s2 : FullState,
            PreservesCoreSlice FullState.core s1 s2 ∧ s2.LengthsOk c ∧
            n2.toNat ≤ c.scratch_cap ∧ tot2.toNat ≤ c.scratch_cap ∧
            5 * n2.toNat + 32 + tot2.toNat ≤ c.scratch_cap ∧ FullExtScratchPres s s2 ∧
            (FullMem c s2 ⋆ R) m2)
          (fun _ ⟨n2, tot2, ch2, ⟨⟩⟩ m2 h => by c0_hsteps; exact hJ2 (n2, tot2, ch2, ()) m2 h)
          (fun J3 hJ3 => ?_)
        c0_hsplit
        · have hoff_le : off.toNat ≤ s.core.wlen := by
            try rw [Nat.mod_eq_of_lt (by omega : s.core.wlen < 2 ^ 64)] at hc
            rw [hoff_raw] at hc; exact hc
          c0_hsplit
          · have hlen_le : len.toNat ≤ s.core.wlen - off.toNat := by
              rw [hoff_raw, hlen_raw] at hc
              try rw [Nat.mod_eq_of_lt (by omega : s.core.wlen < 2 ^ 64)] at hc
              omega
            have hend_eq : (off + len).toNat = off.toNat + len.toNat := by
              rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
            c0_hsteps_nogrp
            refine wp_loop_safety_slice_pure (fullSafetySlice c) s1 R
              (fun s4 (n4, tot4, ch4, k, ()) =>
                off.toNat ≤ k.toNat ∧ k.toNat ≤ off.toNat + len.toNat ∧
                n4.toNat ≤ c.scratch_cap ∧ tot4.toNat ≤ c.scratch_cap ∧
                5 * n4.toNat + 32 + tot4.toNat ≤ c.scratch_cap ∧ FullExtScratchPres s s4)
              (fun (_, _, _, k, ()) => off.toNat + len.toNat - k.toNat)
              (fun J4 hJ4 => by
                c0_hsteps
                exact hJ4 s1 (n, tot, ch, off, ()) m1 hm1 rfl hs1
                  ⟨Nat.le_refl _, by omega, hn1, htot1, hcap1, hpres1⟩)
              (fun J4 s4 (n4, tot4, ch4, k, ()) m4 hcore4 hs4
                  ⟨hk_lo, hk_hi, hn4, htot4, hcap4, hpres4⟩ hm4 hJ4 => ?_)
            dsimp only [fullSafetySlice] at hs4 hm4
            have hceq4 : s4.core = s.core := Eq.trans hcore4 hceq1
            c0_hsplit
            · have hk_lt : k.toNat < off.toNat + len.toNat := by
                rw [hoff_raw, hlen_raw] at hc
                try rw [Nat.mod_eq_of_lt (by omega : off.toNat + len.toNat < 2 ^ 64)] at hc
                exact hc
              c0_hsplit
              · c0_hsteps
                exact hJ3 (n4, tot4, ch4, ()) m4
                  ⟨s4, hcore4, hs4, hn4, htot4, hcap4, hpres4, hm4⟩
              have hk_ws : k.toNat < s4.core.wstk.length := by rw [hceq4, hwsl]; omega
              have hk1 : (k + 1#64).toNat = k.toNat + 1 := m7b_bv64_add1_toNat (by omega)
              c0_hsteps_nogrp
              let w4 := s4.core.wstk[k.toNat]'hk_ws
              have hl_v4 : l.toNat < s4.core.vals.length := by rw [hceq4, hvl]; omega
              refine wp_join_group (ts := [i64, i64, .bool, i64])
                (fun (n5, tot5, ch5, k5, ()) m5 => ∃ s5 : FullState,
                  PreservesCoreSlice FullState.core s4 s5 ∧ s5.LengthsOk c ∧
                  k.toNat < k5.toNat ∧ k5.toNat ≤ off.toNat + len.toNat ∧
                  n5.toNat ≤ c.scratch_cap ∧ tot5.toNat ≤ c.scratch_cap ∧
                  5 * n5.toNat + 32 + tot5.toNat ≤ c.scratch_cap ∧ FullExtScratchPres s s5 ∧
                  (FullMem c s5 ⋆ R) m5)
                (fun _ ⟨n5, tot5, ch5, k5, ⟨⟩⟩ m5
                    ⟨s5, hcore5, hs5, hk5_gt, hk5_hi, hn5, htot5, hcap5, hpres5, hm5⟩ => by
                  c0_hsteps
                  exact hJ4 s5 (n5, tot5, ch5, k5, ()) m5 hm5 (by dsimp only; omega) hcore5 hs5
                    ⟨by omega, hk5_hi, hn5, htot5, hcap5, hpres5⟩)
                (fun J5 hJ5 => ?_)
              c0_hsplit
              · refine wp_join_group (ts := [i64, i64, .bool])
                  (fun (n6, tot6, ch6, ()) m6 => ∃ s6 : FullState,
                    PreservesCoreSlice FullState.core s4 s6 ∧ s6.LengthsOk c ∧
                    n6.toNat ≤ c.scratch_cap ∧ tot6.toNat ≤ c.scratch_cap ∧
                    5 * n6.toNat + 32 + tot6.toNat ≤ c.scratch_cap ∧ FullExtScratchPres s s6 ∧
                    (FullMem c s6 ⋆ R) m6)
                  (fun _ ⟨n6, tot6, ch6, ⟨⟩⟩ m6
                      ⟨s6, hcore6, hs6, hn6, htot6, hcap6, hpres6, hm6⟩ => by
                    c0_hsteps
                    exact hJ5 (n6, tot6, ch6, k + 1#64, ()) m6
                      ⟨s6, hcore6, hs6, by omega, by omega, hn6, htot6, hcap6, hpres6, hm6⟩)
                  (fun J6 hJ6 => ?_)
                c0_hsplit
                · have hot_lt : (w4 &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars := by
                    try rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc
                    try rw [Nat.mod_eq_of_lt (by omega : 2 * s.core.cur_vars < 2 ^ 64)] at hc
                    exact hc
                  c0_hsplit
                  · have hot_v :
                        ((w4 &&& 0x7FFFFFFF#32).setWidth 64).toNat < s4.core.vals.length :=
                      by rw [m7b_zext32, hceq4, hvl]; omega
                    c0_hsplit
                    · refine wp_join_group (ts := []) (fun () m7 => m7 = m4)
                        (fun _ _ m7 hm7 => by
                          subst m7
                          refine wp_join_group (ts := [i64, i64, .bool])
                            (fun (n8, tot8, ch8, ()) m8 => ∃ s8 : FullState,
                              PreservesCoreSlice FullState.core s4 s8 ∧ s8.LengthsOk c ∧
                              n8.toNat ≤ c.scratch_cap ∧ tot8.toNat ≤ c.scratch_cap ∧
                              5 * n8.toNat + 32 + tot8.toNat ≤ c.scratch_cap ∧
                              FullExtScratchPres s s8 ∧ (FullMem c s8 ⋆ R) m8)
                            (fun _ ⟨n8, tot8, ch8, ⟨⟩⟩ m8 h => by
                              c0_hsteps; exact hJ6 (n8, tot8, ch8, ()) m8 h)
                            (fun J8 hJ8 => ?_)
                          c0_hsplit
                          · c0_hsteps; exact hJ8 (n4, tot4, true, ()) m4
                              ⟨s4, rfl, hs4, hn4, htot4, hcap4, hpres4, hm4⟩
                          have hn4p1 : (n4 + 1#64).toNat = n4.toNat + 1 :=
                            m7b_bv64_add1_toNat (by omega)
                          have hn4p1_le : n4.toNat + 1 ≤ c.scratch_cap := by
                            try rw [show (1 : BitVec 64).toNat = 1 from rfl] at hc
                            try rw [Nat.mod_eq_of_lt (by omega : n4.toNat + 1 < 2 ^ 64)] at hc
                            omega
                          c0_hsplit
                          · c0_hsteps; exact hJ8 (n4, tot4, true, ()) m4
                              ⟨s4, rfl, hs4, hn4, htot4, hcap4, hpres4, hm4⟩
                          have htot_p2 : (tot4 + 2#64).toNat = tot4.toNat + 2 := by
                            rw [BitVec.toNat_add, show (2#64 : BitVec 64).toNat = 2 from rfl,
                              Nat.mod_eq_of_lt (by omega)]
                          have htot_le2 : tot4.toNat + 2 ≤ c.scratch_cap := by
                            try rw [show (2 : BitVec 64).toNat = 2 from rfl] at hc
                            try rw [Nat.mod_eq_of_lt (by omega : tot4.toNat + 2 < 2 ^ 64)] at hc
                            omega
                          c0_hsplit
                          · c0_hsteps; exact hJ8 (n4, tot4, true, ()) m4
                              ⟨s4, rfl, hs4, hn4, htot4, hcap4, hpres4, hm4⟩
                          have hcap_new2 : 5 * (n4.toNat + 1) + 32 + (tot4.toNat + 2) ≤
                              c.scratch_cap := by
                            try rw [show (32 : BitVec 64).toNat = 32 from rfl] at hc
                            try rw [show (5 : BitVec 64).toNat = 5 from rfl] at hc
                            try rw [show (1 : BitVec 64).toNat = 1 from rfl] at hc
                            try rw [show (2 : BitVec 64).toNat = 2 from rfl] at hc
                            try rw [Nat.mod_eq_of_lt (by omega : n4.toNat + 1 < 2 ^ 64)] at hc
                            try rw [Nat.mod_eq_of_lt (by omega :
                              5 * (n4.toNat + 1) < 2 ^ 64)] at hc
                            try rw [Nat.mod_eq_of_lt (by omega :
                              32 + 5 * (n4.toNat + 1) < 2 ^ 64)] at hc
                            try rw [Nat.mod_eq_of_lt (by omega :
                              32 + 5 * (n4.toNat + 1) + tot4.toNat < 2 ^ 64)] at hc
                            try rw [Nat.mod_eq_of_lt (by omega :
                              32 + 5 * (n4.toNat + 1) + tot4.toNat + 2 < 2 ^ 64)] at hc
                            omega
                          have hsbl4 := hs4.scratch_ok.scratch_buf_len
                          have hi0_eq := m7b_bv64_32_add_2n (n := n4) (by omega)
                          have hi1_eq := m7b_bv64_32_add_2n1 (n := n4) (by omega)
                          have hi0_lt : (32#64 + (n4 <<< (1 : Nat))).toNat <
                              s4.scratch.scratch_buf.length := by rw [hi0_eq, hsbl4]; omega
                          have hi1_lt : (32#64 + (n4 <<< (1 : Nat)) + 1#64).toNat <
                              (s4.scratch.scratch_buf.set (32#64 + (n4 <<< (1 : Nat))).toNat
                                (l.setWidth 32 ||| 0x80000000#32)).length := by
                            rw [List.length_set, hi1_eq, hsbl4]; omega
                          c0_hsteps
                          exact hJ8 (n4 + 1#64, tot4 + 2#64, ch4, ()) _
                            ⟨{ s4 with scratch := { s4.scratch with
                                scratch_buf := (s4.scratch.scratch_buf.set
                                  (32#64 + (n4 <<< (1 : Nat))).toNat
                                  (l.setWidth 32 ||| 0x80000000#32)).set
                                  (32#64 + (n4 <<< (1 : Nat)) + 1#64).toNat
                                  (w4 &&& 0x7FFFFFFF#32) } },
                              rfl, m7b_len_scrBuf (m7b_len_scrBuf hs4),
                              by rw [hn4p1]; exact hn4p1_le, by rw [htot_p2]; exact htot_le2,
                              by rw [hn4p1, htot_p2]; exact hcap_new2,
                              ⟨hpres4.1, hpres4.2⟩, hm⟩)
                        (fun J7 hJ7 => by
                          c0_hsplit
                          · c0_hsteps; exact hJ7 () m4 rfl
                          c0_hsplit
                          · c0_hsteps; exact hJ7 () m4 rfl
                          · c0_hsteps
                            exact hJ6 (n4, tot4, ch4, ()) m4
                              ⟨s4, rfl, hs4, hn4, htot4, hcap4, hpres4, hm4⟩)
                    · c0_hsteps; exact hJ6 (n4, tot4, ch4, ()) m4
                        ⟨s4, rfl, hs4, hn4, htot4, hcap4, hpres4, hm4⟩
                  · c0_hsteps; exact hJ6 (n4, tot4, ch4, ()) m4
                      ⟨s4, rfl, hs4, hn4, htot4, hcap4, hpres4, hm4⟩
                · c0_hsteps; exact hJ6 (n4, tot4, ch4, ()) m4
                    ⟨s4, rfl, hs4, hn4, htot4, hcap4, hpres4, hm4⟩
              · refine wp_join_group (ts := [i64])
                  (fun (k6, ()) m6 =>
                    m6 = m4 ∧ k.toNat < k6.toNat ∧ k6.toNat ≤ off.toNat + len.toNat)
                  (fun _ ⟨k6, ⟨⟩⟩ m6 ⟨hm6, h1, h2⟩ => by
                    subst m6
                    c0_hsteps
                    exact hJ5 (n4, tot4, ch4, k6, ()) m4
                      ⟨s4, rfl, hs4, h1, h2, hn4, htot4, hcap4, hpres4, hm4⟩)
                  (fun J6 hJ6 => by
                    c0_hsplit
                    · have hk2_eq : (k + 1#64 + 1#64).toNat = k.toNat + 2 := by
                        rw [BitVec.toNat_add, hk1, show (1#64 : BitVec 64).toNat = 1 from rfl,
                          Nat.mod_eq_of_lt (by omega)]
                      have hk2_le : k.toNat + 2 ≤ off.toNat + len.toNat := by
                        rw [hoff_raw, hlen_raw] at hc
                        try rw [show (1 : BitVec 64).toNat = 1 from rfl] at hc
                        try rw [Nat.mod_eq_of_lt (by omega : k.toNat + 1 < 2 ^ 64)] at hc
                        try rw [Nat.mod_eq_of_lt (by omega : k.toNat + 2 < 2 ^ 64)] at hc
                        try rw [Nat.mod_eq_of_lt (by omega : off.toNat + len.toNat < 2 ^ 64)]
                          at hc
                        omega
                      c0_hsteps; exact hJ6 (k + 1#64 + 1#64, ()) m4
                        ⟨rfl, by rw [hk2_eq]; omega, by rw [hk2_eq]; omega⟩
                    · c0_hsteps; exact hJ6 (k + 1#64, ()) m4
                        ⟨rfl, by rw [hk1]; omega, by rw [hk1]; omega⟩)
            · c0_hsteps; exact hJ3 (n4, tot4, ch4, ()) m4
                ⟨s4, hcore4, hs4, hn4, htot4, hcap4, hpres4, hm4⟩
          · c0_hsteps
            exact hJ3 (n, tot, ch, ()) m1 ⟨s1, rfl, hs1, hn1, htot1, hcap1, hpres1, hm1⟩
        · c0_hsteps
          exact hJ3 (n, tot, ch, ()) m1 ⟨s1, rfl, hs1, hn1, htot1, hcap1, hpres1, hm1⟩
      · c0_hsteps; exact hJ2 (n, tot, ch, ()) m1 ⟨s1, rfl, hs1, hn1, htot1, hcap1, hpres1, hm1⟩
    · c0_hsteps; exact hJ1 () m1 rfl

private theorem m7b_ok_tr {c : FullCfg} {s : FullState} {i : Nat} {v : BitVec 32}
    (h : s.LengthsOk c) :
    ({ s with scratch :=
        { s.scratch with tarjan_reach := s.scratch.tarjan_reach.set i v } }).LengthsOk c :=
  ⟨h.core_ok, { h.scratch_ok with
    tarjan_reach_len := by rw [List.length_set, h.scratch_ok.tarjan_reach_len] }⟩

private theorem m7b_ok_ws1 {c : FullCfg} {s : FullState} {i : Nat} {v : BitVec 32}
    (h : s.LengthsOk c) :
    ({ s with scratch :=
        { s.scratch with work_stk1 := s.scratch.work_stk1.set i v } }).LengthsOk c :=
  ⟨h.core_ok, { h.scratch_ok with
    work_stk1_len := by rw [List.length_set, h.scratch_ok.work_stk1_len] }⟩

private theorem m7b_ok_ws2 {c : FullCfg} {s : FullState} {i : Nat} {v : BitVec 32}
    (h : s.LengthsOk c) :
    ({ s with scratch :=
        { s.scratch with work_stk2 := s.scratch.work_stk2.set i v } }).LengthsOk c :=
  ⟨h.core_ok, { h.scratch_ok with
    work_stk2_len := by rw [List.length_set, h.scratch_ok.work_stk2_len] }⟩

private theorem m7b_ok_wsort {c : FullCfg} {s : FullState} {i : Nat} {v : BitVec 32}
    (h : s.LengthsOk c) :
    ({ s with scratch :=
        { s.scratch with wsort := s.scratch.wsort.set i v } }).LengthsOk c :=
  ⟨h.core_ok, { h.scratch_ok with
    wsort_len := by rw [List.length_set, h.scratch_ok.wsort_len] }⟩

private theorem m7b_bv32_xor1_lt {x : BitVec 32} {n : Nat} (hx : x.toNat < 2 * n) :
    (x ^^^ 1#32).toNat < 2 * n := by
  rw [BitVec.toNat_xor, show (1#32 : BitVec 32).toNat = 1 from rfl]
  have h : x.toNat ^^^ 1 = if x.toNat % 2 = 0 then x.toNat + 1 else x.toNat - 1 := by
    apply Nat.eq_of_testBit_eq
    intro i
    cases i with
    | zero =>
      rw [Nat.testBit_xor]
      cases h0 : Nat.mod_two_eq_zero_or_one x.toNat <;> simp_all <;> omega
    | succ k =>
      have hbit1 : (1 : Nat).testBit (k + 1) = false := by
        rw [Nat.testBit_succ, show 1 / 2 = 0 from rfl, Nat.zero_testBit]
      rw [Nat.testBit_xor, hbit1, Bool.xor_false]
      split
      · rw [Nat.testBit_succ, Nat.testBit_succ, show (x.toNat + 1) / 2 = x.toNat / 2 by omega]
      · rw [Nat.testBit_succ, Nat.testBit_succ, show (x.toNat - 1) / 2 = x.toNat / 2 by omega]
  rw [h]; split <;> omega

private theorem m7b_bv64_add2_toNat {a b : BitVec 64} (h : a.toNat + b.toNat < 2 ^ 64) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

private theorem m7b_bv32_add1_lt {k s : BitVec 32} (h : k.toNat < s.toNat) :
    (k + 1#32).toNat = k.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
    Nat.mod_eq_of_lt (by have := s.isLt; omega)]

public theorem full_walk_build_occ_m7_wp (Γ : Env) :
    ∀ (args : Tup Val [i64, i64]) (m : Mem 64) (Q : Post [i64]) (X : XPost),
      m7BuildOccSpec args m Q X → Func.wp Γ full_walk_build_occ_m7_body args m Q X := by
  rw [m7BuildOccSpec_eq]
  rintro ⟨h, ncl, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hlen hm hQ
  dsimp only [Func.wp, full_walk_build_occ_m7_body]
  have hdb : LratBytes.dimacsBound = 2 ^ 28 := rfl
  have hmax : c.max_vars < 2 * 2 ^ 28 := by simpa only [hdb] using c.hmaxv
  have haca : c.arena_cap < 2 * 2 ^ 28 := by simpa only [hdb] using c.harena
  have hwc : c.wcap < 2 * 2 ^ 28 := by simpa only [hdb] using c.hwcap
  have hscr : c.scratch_cap < 2 ^ 28 := by simpa only [hdb] using c.hscr
  have hcv_le := hlen.core_ok.cur_vars_le
  have harl := hlen.core_ok.arena_len_arr
  have hale := hlen.core_ok.arena_len_le
  have hvl := hlen.core_ok.vals_len
  have hsbl := hlen.scratch_ok.scratch_buf_len
  have htrl := hlen.scratch_ok.tarjan_reach_len
  have hmkl := hlen.scratch_ok.tarjan_mark_len
  have hws1 := hlen.scratch_ok.work_stk1_len
  have hwvs := hlen.scratch_ok.walk_vals_len
  c0_hsplit
  · c0_hsteps; exact hQ (0#64, ()) s m rfl hlen ⟨m7b_ext_refl s, Nat.zero_le _⟩ hm
  have hcv_pos : 0 < s.core.cur_vars := by
    apply Nat.pos_of_ne_zero; intro h0
    apply hc; rw [h0]; rfl
  c0_hsplit
  · c0_hsteps; exact hQ (0#64, ()) s m rfl hlen ⟨m7b_ext_refl s, Nat.zero_le _⟩ hm
  have hcv_ok : s.core.cur_vars ≤ c.max_vars := by
    try rw [Nat.mod_eq_of_lt (by omega : c.max_vars < 2 ^ 64)] at hc
    try rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc
    omega
  c0_hsplit
  · c0_hsteps; exact hQ (0#64, ()) s m rfl hlen ⟨m7b_ext_refl s, Nat.zero_le _⟩ hm
  have hncl_pos : 0 < ncl.toNat := by
    apply Nat.pos_of_ne_zero; intro h0
    apply hc; exact BitVec.eq_of_toNat_eq (by simpa using h0)
  c0_hsplit
  · c0_hsteps; exact hQ (0#64, ()) s m rfl hlen ⟨m7b_ext_refl s, Nat.zero_le _⟩ hm
  have hncl_le : ncl.toNat ≤ c.scratch_cap := by
    try rw [Nat.mod_eq_of_lt (by omega : c.scratch_cap < 2 ^ 64)] at hc
    omega
  c0_hsplit
  · c0_hsteps; exact hQ (0#64, ()) s m rfl hlen ⟨m7b_ext_refl s, Nat.zero_le _⟩ hm
  have hcap_ok : 32 + 5 * ncl.toNat ≤ c.scratch_cap := by
    try rw [show (32 : BitVec 64).toNat = 32 from rfl] at hc
    try rw [show (5 : BitVec 64).toNat = 5 from rfl] at hc
    try rw [Nat.mod_eq_of_lt (by omega : c.scratch_cap < 2 ^ 64)] at hc
    try rw [Nat.mod_eq_of_lt (by omega : 5 * ncl.toNat < 2 ^ 64)] at hc
    try rw [Nat.mod_eq_of_lt (by omega : 32 + 5 * ncl.toNat < 2 ^ 64)] at hc
    omega
  have h2cv_eq : (BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat)).toNat =
      2 * s.core.cur_vars := by
    rw [BitVec.toNat_shiftLeft, m7b_bv64_ofNat_eq (by omega), Nat.shiftLeft_eq]
    omega
  let v21 := 32#64 + (ncl <<< (1 : Nat))
  let v22 := v21 + ncl
  let v23 := v22 + ncl
  let v24 := v23 + ncl
  let v25 := BitVec.ofNat 64 c.scratch_cap - v24
  have hv21 : v21.toNat = 32 + 2 * ncl.toNat := by
    dsimp only [v21]
    rw [BitVec.toNat_add, m7b_bv64_shl1_toNat (by omega),
      show (32#64 : BitVec 64).toNat = 32 from rfl, Nat.mod_eq_of_lt (by omega)]
  have hv22 : v22.toNat = 32 + 3 * ncl.toNat := by
    dsimp only [v22]; rw [m7b_bv64_add2_toNat (by rw [hv21]; omega), hv21]; omega
  have hv23 : v23.toNat = 32 + 4 * ncl.toNat := by
    dsimp only [v23]; rw [m7b_bv64_add2_toNat (by rw [hv22]; omega), hv22]; omega
  have hv24 : v24.toNat = 32 + 5 * ncl.toNat := by
    dsimp only [v24]; rw [m7b_bv64_add2_toNat (by rw [hv23]; omega), hv23]; omega
  have hv25 : v25.toNat = c.scratch_cap - (32 + 5 * ncl.toNat) := by
    dsimp only [v25]
    rw [BitVec.toNat_sub, m7b_bv64_ofNat_eq (by omega), hv24,
      show (2 ^ 64 - (32 + 5 * ncl.toNat) + c.scratch_cap) % 2 ^ 64 =
        c.scratch_cap - (32 + 5 * ncl.toNat) by omega]
  c0_hsteps_nogrp
  -- Pass 1 (`J0`: `(ulen, ci)` for `ci < ncl`)
  refine wp_loop_safety_slice_pure (fullSafetySlice c) s R
    (fun s1 (ulen, ci, ()) =>
      ulen.toNat ≤ ncl.toNat ∧ ci.toNat ≤ ncl.toNat ∧ FullExtScratchPres s s1)
    (fun (_, ci, ()) => ncl.toNat - ci.toNat)
    (fun J0 hJ0 => by
      c0_hsteps
      exact hJ0 s (0#64, 0#64, ()) m hm rfl hlen
        ⟨Nat.zero_le _, Nat.zero_le _, m7b_ext_refl s⟩)
    (fun J0 s1 (ulen, ci, ()) m1 hcore1 hs1 ⟨hulen_le, hci_le, hpres1⟩ hm1 hJ0 => ?_)
  dsimp only [fullSafetySlice] at hs1 hm1
  have hceq1 : s1.core = s.core := hcore1
  c0_hsplit
  · -- Pass 1 body (`ci < ncl`)
    have hci_lt : ci.toNat < ncl.toNat := by exact hc
    have hi0_eq := m7b_bv64_32_add_2n (n := ci) (by omega)
    have hi1_eq := m7b_bv64_32_add_2n1 (n := ci) (by omega)
    have hsbl1 := hs1.scratch_ok.scratch_buf_len
    have hi0_sb : (32#64 + (ci <<< (1 : Nat))).toNat < s1.scratch.scratch_buf.length := by
      rw [hi0_eq, hsbl1]; omega
    have hi1_sb : (32#64 + (ci <<< (1 : Nat)) + 1#64).toNat <
        s1.scratch.scratch_buf.length := by
      rw [hi1_eq, hsbl1]; omega
    c0_hsteps_nogrp
    let e0 := s1.scratch.scratch_buf[(32#64 + (ci <<< (1 : Nat))).toNat]'hi0_sb
    let e1 := s1.scratch.scratch_buf[(32#64 + (ci <<< (1 : Nat)) + 1#64).toNat]'hi1_sb
    have he0_def : s1.scratch.scratch_buf[(BitVec.toNat (32 : BitVec 64) +
        2 * ci.toNat) % 2 ^ 64]'(by
          rw [show BitVec.toNat (32 : BitVec 64) = 32 from rfl,
            Nat.mod_eq_of_lt (by omega : 32 + 2 * ci.toNat < 2 ^ 64), hsbl1]; omega) =
        e0 := by
      dsimp only [e0]; congr 1
      rw [hi0_eq, show BitVec.toNat (32 : BitVec 64) = 32 from rfl, Nat.mod_eq_of_lt (by omega)]
    have he1_def : s1.scratch.scratch_buf[(BitVec.toNat (32 : BitVec 64) +
        2 * ci.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
          rw [show BitVec.toNat (32 : BitVec 64) = 32 from rfl,
            show BitVec.toNat (1 : BitVec 64) = 1 from rfl,
            Nat.mod_eq_of_lt (by omega : 32 + 2 * ci.toNat + 1 < 2 ^ 64), hsbl1]; omega) =
        e1 := by
      dsimp only [e1]; congr 1
      rw [hi1_eq, show BitVec.toNat (32 : BitVec 64) = 32 from rfl,
        show BitVec.toNat (1 : BitVec 64) = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
    refine wp_join_group (ts := [i32])
      (fun (sat, ()) m2 => ∃ s2 : FullState,
        PreservesCoreSlice FullState.core s1 s2 ∧ s2.LengthsOk c ∧
        FullExtScratchPres s s2 ∧ (FullMem c s2 ⋆ R) m2)
      (fun _ ⟨sat, ⟨⟩⟩ m2 ⟨s2, hcore2, hs2, hpres2, hm2⟩ => by
        have hceq2 : s2.core = s.core := Eq.trans hcore2 hceq1
        have hv21_ci : (v21 + ci).toNat = 32 + 2 * ncl.toNat + ci.toNat := by
          rw [m7b_bv64_add2_toNat (by rw [hv21]; omega), hv21]
        have hsbl2 := hs2.scratch_ok.scratch_buf_len
        have hv21_sb : (v21 + ci).toNat < s2.scratch.scratch_buf.length := by
          rw [hv21_ci, hsbl2]; omega
        c0_hsteps_nogrp
        let s3 : FullState := { s2 with scratch :=
          { s2.scratch with scratch_buf := s2.scratch.scratch_buf.set (v21 + ci).toNat sat } }
        have hs3 : s3.LengthsOk c := m7b_len_scrBuf hs2
        have hpres3 : FullExtScratchPres s s3 := ⟨hpres2.1, hpres2.2⟩
        refine wp_join_group (ts := [i64])
          (fun (ulen', ()) m4 => ∃ s4 : FullState,
            PreservesCoreSlice FullState.core s3 s4 ∧ s4.LengthsOk c ∧
            ulen'.toNat ≤ ncl.toNat ∧ FullExtScratchPres s s4 ∧ (FullMem c s4 ⋆ R) m4)
          (fun _ ⟨ulen', ⟨⟩⟩ m4 ⟨s4, hcore4, hs4, hu4, hpres4, hm4⟩ => by
            have hci1 : (ci + 1#64).toNat = ci.toNat + 1 := m7b_bv64_add1_toNat (by omega)
            c0_hsteps
            exact hJ0 s4 (ulen', ci + 1#64, ()) m4 hm4 (by dsimp only; omega)
              (Eq.trans hcore4 hcore2) hs4 ⟨hu4, by rw [hci1]; omega, hpres4⟩)
          (fun J2 hJ2 => by
            have hsbl3 := hs3.scratch_ok.scratch_buf_len
            have hv22_ci : (v22 + ci).toNat = 32 + 3 * ncl.toNat + ci.toNat := by
              rw [m7b_bv64_add2_toNat (by rw [hv22]; omega), hv22]
            have hv22_sb : (v22 + ci).toNat < s3.scratch.scratch_buf.length := by
              rw [hv22_ci, hsbl3]; omega
            refine wp_join_group (ts := []) (fun () m3b => (FullMem c s3 ⋆ R) m3b)
              (fun _ _ m3b hm3b => by
                c0_hsteps
                exact hJ2 (ulen, ()) _
                  ⟨{ s3 with scratch := { s3.scratch with
                      scratch_buf := s3.scratch.scratch_buf.set (v22 + ci).toNat
                        0xFFFFFFFF#32 } },
                    rfl, m7b_len_scrBuf hs3, hulen_le, ⟨hpres3.1, hpres3.2⟩, hm⟩)
              (fun J3 hJ3 => by
                c0_hsplit
                · c0_hsplit
                  · have hul_lt : ulen.toNat < ncl.toNat := by exact hc
                    have hv23_ul : (v23 + ulen).toNat = 32 + 4 * ncl.toNat + ulen.toNat := by
                      rw [m7b_bv64_add2_toNat (by rw [hv23]; omega), hv23]
                    have hv23_sb : (v23 + ulen).toNat < (s3.scratch.scratch_buf.set
                        (v22 + ci).toNat (ulen.setWidth 32)).length := by
                      rw [List.length_set, hv23_ul, hsbl3]; omega
                    have hu1 : (ulen + 1#64).toNat = ulen.toNat + 1 :=
                      m7b_bv64_add1_toNat (by omega)
                    c0_hsteps
                    exact hJ2 (ulen + 1#64, ()) _
                      ⟨{ s3 with scratch := { s3.scratch with
                          scratch_buf := (s3.scratch.scratch_buf.set (v22 + ci).toNat
                            (ulen.setWidth 32)).set (v23 + ulen).toNat (ci.setWidth 32) } },
                        rfl, m7b_len_scrBuf (m7b_len_scrBuf hs3),
                        by rw [hu1]; omega, ⟨hpres3.1, hpres3.2⟩, hm⟩
                  · c0_hsteps; exact hJ3 () _ hm
                · c0_hsteps; exact hJ3 () _ hm)))
      (fun J1 hJ1 => ?_)
    c0_hsplit
    · -- Binary clause `e0 & 0x80000000 != 0`
      let la := e0 &&& 0x7FFFFFFF#32
      refine wp_join_group (ts := [i32])
        (fun (satA, ()) mA => ∃ sA : FullState,
          PreservesCoreSlice FullState.core s1 sA ∧ sA.LengthsOk c ∧
          FullExtScratchPres s sA ∧ (FullMem c sA ⋆ R) mA)
        (fun _ ⟨satA, ⟨⟩⟩ mA ⟨sA, hcoreA, hsA, hpresA, hmA⟩ => by
          have hceqA : sA.core = s.core := Eq.trans hcoreA hceq1
          refine wp_join_group (ts := [i32])
            (fun (satB, ()) mB => ∃ sB : FullState,
              PreservesCoreSlice FullState.core sA sB ∧ sB.LengthsOk c ∧
              FullExtScratchPres s sB ∧ (FullMem c sB ⋆ R) mB)
            (fun _ ⟨satB, ⟨⟩⟩ mB ⟨sB, hcoreB, hsB, hpresB, hmB⟩ => by
              c0_hsteps
              exact hJ1 (satB, ()) mB ⟨sB, Eq.trans hcoreB hcoreA, hsB, hpresB, hmB⟩)
            (fun J3 hJ3 => by
              c0_hsplit
              · have he1_lt : e1.toNat < 2 * s.core.cur_vars := by
                  rw [he1_def] at hc
                  try rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc
                  try rw [Nat.mod_eq_of_lt (by omega : 2 * s.core.cur_vars < 2 ^ 64)] at hc
                  exact hc
                have he1_v : (e1.setWidth 64).toNat < sA.core.vals.length := by
                  rw [m7b_zext32, hceqA, hvl]; omega
                c0_hsplit
                · have he1_tr : (e1.setWidth 64).toNat < sA.scratch.tarjan_reach.length := by
                    rw [m7b_zext32, hsA.scratch_ok.tarjan_reach_len]; omega
                  have he1_wv : (e1.setWidth 64).toNat < sA.scratch.walk_vals.length := by
                    rw [m7b_zext32, hsA.scratch_ok.walk_vals_len]; omega
                  c0_hsteps_nogrp
                  let sB : FullState := { sA with scratch :=
                    { sA.scratch with
                        tarjan_reach := sA.scratch.tarjan_reach.set (e1.setWidth 64).toNat
                          (sA.scratch.tarjan_reach[(e1.setWidth 64).toNat]'he1_tr + 1#32) } }
                  have hsB : sB.LengthsOk c := m7b_ok_tr hsA
                  have hpresB : FullExtScratchPres s sB := ⟨hpresA.1, hpresA.2⟩
                  c0_hsteps <;>
                    first
                    | exact hJ3 (satA + 1#32, ()) _ ⟨sB, rfl, hsB, hpresB, hm⟩
                    | exact hJ3 (satA, ()) _ ⟨sB, rfl, hsB, hpresB, hm⟩
                · c0_hsteps; exact hJ3 (satA, ()) mA ⟨sA, rfl, hsA, hpresA, hmA⟩
              · c0_hsteps; exact hJ3 (satA, ()) mA ⟨sA, rfl, hsA, hpresA, hmA⟩))
        (fun J2 hJ2 => by
          c0_hsplit
          · have hla_lt : la.toNat < 2 * s.core.cur_vars := by
              rw [he0_def] at hc; dsimp only [la]
              try rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc
              try rw [Nat.mod_eq_of_lt (by omega : 2 * s.core.cur_vars < 2 ^ 64)] at hc
              exact hc
            have hla_v : (la.setWidth 64).toNat < s1.core.vals.length := by
              rw [m7b_zext32, hceq1, hvl]; omega
            c0_hsplit
            · have hla_tr : (la.setWidth 64).toNat < s1.scratch.tarjan_reach.length := by
                rw [m7b_zext32, hs1.scratch_ok.tarjan_reach_len]; omega
              have hla_wv : (la.setWidth 64).toNat < s1.scratch.walk_vals.length := by
                rw [m7b_zext32, hs1.scratch_ok.walk_vals_len]; omega
              c0_hsteps_nogrp
              let sA : FullState := { s1 with scratch :=
                { s1.scratch with
                    tarjan_reach := s1.scratch.tarjan_reach.set (la.setWidth 64).toNat
                      (s1.scratch.tarjan_reach[(la.setWidth 64).toNat]'hla_tr + 1#32) } }
              have hsA : sA.LengthsOk c := m7b_ok_tr hs1
              have hpresA : FullExtScratchPres s sA := ⟨hpres1.1, hpres1.2⟩
              c0_hsteps <;>
                first
                | exact hJ2 (0#32 + 1#32, ()) _ ⟨sA, rfl, hsA, hpresA, hm⟩
                | exact hJ2 (0#32, ()) _ ⟨sA, rfl, hsA, hpresA, hm⟩
            · c0_hsteps; exact hJ2 (0#32, ()) m1 ⟨s1, rfl, hs1, hpres1, hm1⟩
          · c0_hsteps; exact hJ2 (0#32, ()) m1 ⟨s1, rfl, hs1, hpres1, hm1⟩)
    · -- Large clause (`e0` is arena ref)
      refine wp_join_group (ts := [i32])
        (fun (sat, ()) m2 => ∃ s2 : FullState,
          PreservesCoreSlice FullState.core s1 s2 ∧ s2.LengthsOk c ∧
          FullExtScratchPres s s2 ∧ (FullMem c s2 ⋆ R) m2)
        (fun _ ⟨sat, ⟨⟩⟩ m2 h => by c0_hsteps; exact hJ1 (sat, ()) m2 h)
        (fun J2 hJ2 => ?_)
      c0_hsplit
      · have he0_3 : e0.toNat + 3 ≤ s.core.arena_len := by
          rw [he0_def] at hc
          try rw [show (3 : BitVec 64).toNat = 3 from rfl] at hc
          try rw [Nat.mod_eq_of_lt (by have := e0.isLt; omega)] at hc
          try rw [Nat.mod_eq_of_lt (by omega : s.core.arena_len < 2 ^ 64)] at hc
          exact hc
        have he02_ar : (e0.setWidth 64 + 2#64).toNat < s1.core.arena.length := by
          rw [BitVec.toNat_add, m7b_zext32, show (2#64 : BitVec 64).toNat = 2 from rfl,
            Nat.mod_eq_of_lt (by omega), hceq1, harl]; omega
        c0_hsteps_nogrp
        let sz := s1.core.arena[(e0.setWidth 64 + 2#64).toNat]'he02_ar
        have hsz_def : s1.core.arena[(e0.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by
            rw [show BitVec.toNat (2 : BitVec 64) = 2 from rfl,
              Nat.mod_eq_of_lt (by omega : e0.toNat + 2 < 2 ^ 64), hceq1, harl]
            omega) = sz := by
          dsimp only [sz]; congr 1
        refine wp_join_group (ts := [i32])
          (fun (sat, ()) m2 => ∃ s2 : FullState,
            PreservesCoreSlice FullState.core s1 s2 ∧ s2.LengthsOk c ∧
            FullExtScratchPres s s2 ∧ (FullMem c s2 ⋆ R) m2)
          (fun _ ⟨sat, ⟨⟩⟩ m2 h => by c0_hsteps; exact hJ2 (sat, ()) m2 h)
          (fun J3 hJ3 => ?_)
        c0_hsplit
        · c0_hsplit
          · have he0sz : e0.toNat + 3 + sz.toNat ≤ s.core.arena_len := by
              simp only [he0_def, hsz_def] at hc
              try rw [show (3 : BitVec 64).toNat = 3 from rfl] at hc
              try rw [Nat.mod_eq_of_lt (by omega : e0.toNat + 3 < 2 ^ 64)] at hc
              try rw [Nat.mod_eq_of_lt (by have := sz.isLt; omega)] at hc
              try rw [Nat.mod_eq_of_lt (by omega : s.core.arena_len < 2 ^ 64)] at hc
              exact hc
            c0_hsteps_nogrp
            refine wp_loop_safety_slice_pure (fullSafetySlice c) s1 R
              (fun sK (_sat, k, ()) => k.toNat ≤ sz.toNat ∧ FullExtScratchPres s sK)
              (fun (_, k, ()) => sz.toNat - k.toNat)
              (fun J4 hJ4 => by
                c0_hsteps; exact hJ4 s1 (0#32, 0#32, ()) m1 hm1 rfl hs1
                  ⟨Nat.zero_le _, hpres1⟩)
              (fun J4 sK (satK, k, ()) mK hcoreK hsK ⟨hk_le, hpresK⟩ hmK hJ4 => ?_)
            dsimp only [fullSafetySlice] at hsK hmK
            have hceqK : sK.core = s.core := Eq.trans hcoreK hceq1
            c0_hsplit
            · have hk_lt : k.toNat < sz.toNat := by
                simp only [he0_def, hsz_def] at hc; exact hc
              have hk1 : (k + 1#32).toNat = k.toNat + 1 := m7b_bv32_add1_lt hk_lt
              have hl_ar : (e0.setWidth 64 + 3#64 + k.setWidth 64).toNat <
                  sK.core.arena.length := by
                rw [BitVec.toNat_add, BitVec.toNat_add, m7b_zext32, m7b_zext32,
                  show (3#64 : BitVec 64).toNat = 3 from rfl,
                  Nat.mod_eq_of_lt (by omega : e0.toNat + 3 < 2 ^ 64),
                  Nat.mod_eq_of_lt (by omega : e0.toNat + 3 + k.toNat < 2 ^ 64),
                  hceqK, harl]; omega
              c0_hsteps_nogrp
              let lit := sK.core.arena[(e0.setWidth 64 + 3#64 + k.setWidth 64).toNat]'hl_ar
              refine wp_join_group (ts := [i32])
                (fun (satN, ()) mN => ∃ sN : FullState,
                  PreservesCoreSlice FullState.core sK sN ∧ sN.LengthsOk c ∧
                  FullExtScratchPres s sN ∧ (FullMem c sN ⋆ R) mN)
                (fun _ ⟨satN, ⟨⟩⟩ mN ⟨sN, hcoreN, hsN, hpresN, hmN⟩ => by
                  c0_hsteps
                  exact hJ4 sN (satN, k + 1#32, ()) mN hmN (by dsimp only; rw [hk1]; omega)
                    hcoreN hsN ⟨by rw [hk1]; omega, hpresN⟩)
                (fun J5 hJ5 => by
                  have hlit_def : sK.core.arena[(e0.toNat + BitVec.toNat (3 : BitVec 64) +
                      k.toNat) % 2 ^ 64]'(by
                        rw [show BitVec.toNat (3 : BitVec 64) = 3 from rfl,
                          Nat.mod_eq_of_lt (by omega : e0.toNat + 3 + k.toNat < 2 ^ 64),
                          hceqK, harl]; omega) = lit := by
                    dsimp only [lit]; congr 1
                    rw [BitVec.toNat_add, BitVec.toNat_add, m7b_zext32, m7b_zext32,
                      show BitVec.toNat (3 : BitVec 64) = 3 from rfl,
                      show (3#64 : BitVec 64).toNat = 3 from rfl,
                      Nat.mod_eq_of_lt (by omega : e0.toNat + 3 < 2 ^ 64)]
                  c0_hsplit
                  · have hlit_lt : lit.toNat < 2 * s.core.cur_vars := by
                      simp only [he0_def, hlit_def] at hc
                      try rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc
                      try rw [Nat.mod_eq_of_lt (by omega : 2 * s.core.cur_vars < 2 ^ 64)] at hc
                      exact hc
                    have hlit_v : (lit.setWidth 64).toNat < sK.core.vals.length := by
                      rw [m7b_zext32, hceqK, hvl]; omega
                    c0_hsplit
                    · have hlit_tr : (lit.setWidth 64).toNat <
                          sK.scratch.tarjan_reach.length := by
                        rw [m7b_zext32, hsK.scratch_ok.tarjan_reach_len]; omega
                      have hlit_wv : (lit.setWidth 64).toNat < sK.scratch.walk_vals.length := by
                        rw [m7b_zext32, hsK.scratch_ok.walk_vals_len]; omega
                      c0_hsteps_nogrp
                      let sN : FullState := { sK with scratch :=
                        { sK.scratch with
                            tarjan_reach := sK.scratch.tarjan_reach.set (lit.setWidth 64).toNat
                              (sK.scratch.tarjan_reach[(lit.setWidth 64).toNat]'hlit_tr + 1#32) } }
                      have hsN : sN.LengthsOk c := m7b_ok_tr hsK
                      have hpresN : FullExtScratchPres s sN := ⟨hpresK.1, hpresK.2⟩
                      c0_hsteps <;>
                        first
                        | exact hJ5 (satK + 1#32, ()) _ ⟨sN, rfl, hsN, hpresN, hm⟩
                        | exact hJ5 (satK, ()) _ ⟨sN, rfl, hsN, hpresN, hm⟩
                    · c0_hsteps; exact hJ5 (satK, ()) mK ⟨sK, rfl, hsK, hpresK, hmK⟩
                  · c0_hsteps; exact hJ5 (satK, ()) mK ⟨sK, rfl, hsK, hpresK, hmK⟩)
            · c0_hsteps; exact hJ3 (satK, ()) mK ⟨sK, hcoreK, hsK, hpresK, hmK⟩
          · c0_hsteps; exact hJ3 (0#32, ()) m1 ⟨s1, rfl, hs1, hpres1, hm1⟩
        · c0_hsteps; exact hJ3 (0#32, ()) m1 ⟨s1, rfl, hs1, hpres1, hm1⟩
      · c0_hsteps; exact hJ2 (0#32, ()) m1 ⟨s1, rfl, hs1, hpres1, hm1⟩
  · -- Pass 1 done (`ci ≥ ncl`): enter Pass 2 (`J1`: `(off, l)` for `l < 2 * cur_vars`)
    c0_hsteps_nogrp
    refine wp_loop_safety_slice_pure (fullSafetySlice c) s1 R
      (fun s2 (off, l, ()) =>
        off.toNat ≤ v25.toNat ∧ l.toNat ≤ 2 * s.core.cur_vars ∧ FullExtScratchPres s s2)
      (fun (_, l, ()) => 2 * s.core.cur_vars - l.toNat)
      (fun J1 hJ1 => by
        c0_hsteps
        exact hJ1 s1 (0#64, 0#64, ()) m1 hm1 rfl hs1
          ⟨Nat.zero_le _, Nat.zero_le _, hpres1⟩)
      (fun J1 s2 (off, l, ()) m2 hcore2 hs2 ⟨hoff_le, hl_le, hpres2⟩ hm2 hJ1 => ?_)
    dsimp only [fullSafetySlice] at hs2 hm2
    have hceq2 : s2.core = s.core := Eq.trans hcore2 hceq1
    c0_hsplit
    · have hl_lt : l.toNat < 2 * s.core.cur_vars := by
        try rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc
        try rw [Nat.mod_eq_of_lt (by omega : 2 * s.core.cur_vars < 2 ^ 64)] at hc
        exact hc
      have hl_tr : l.toNat < s2.scratch.tarjan_reach.length := by
        rw [hs2.scratch_ok.tarjan_reach_len]; omega
      c0_hsteps_nogrp
      let deg := s2.scratch.tarjan_reach[l.toNat]'hl_tr
      refine wp_join_group (ts := [i64])
        (fun (off_c, ()) ma => ma = m2 ∧ off_c.toNat ≤ v25.toNat)
        (fun _ ⟨off_c, ⟨⟩⟩ ma ⟨hma, hoffc_le⟩ => by
          subst ma
          refine wp_join_group (ts := [i64])
            (fun (taken, ()) m3 => ∃ s3 : FullState,
              PreservesCoreSlice FullState.core s2 s3 ∧ s3.LengthsOk c ∧
              off_c.toNat + taken.toNat ≤ v25.toNat ∧ FullExtScratchPres s s3 ∧
              (FullMem c s3 ⋆ R) m3)
            (fun _ ⟨taken, ⟨⟩⟩ m3 ⟨s3, hcore3, hs3, htot_le, hpres3, hm3⟩ => by
              have hl_tmk : l.toNat < s3.scratch.tarjan_mark.length := by
                rw [hs3.scratch_ok.tarjan_mark_len]; omega
              have hl_wsrt : l.toNat < s3.scratch.wsort.length := by
                rw [hs3.scratch_ok.wsort_len]; omega
              let s3' : FullState := { s3 with scratch := { s3.scratch with
                tarjan_mark := s3.scratch.tarjan_mark.set l.toNat (off_c.setWidth 32)
                wsort := s3.scratch.wsort.set l.toNat (off_c.setWidth 32) } }
              have hs3' : s3'.LengthsOk c := m7b_ok_wsort (m7b_len_tmk hs3)
              have hl1 : (l + 1#64).toNat = l.toNat + 1 := m7b_bv64_add1_toNat (by omega)
              have hoff1 : (off_c + taken).toNat = off_c.toNat + taken.toNat := by
                rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
              dsimp only
              c0_hsteps
              exact hJ1 s3' (off_c + taken, l + 1#64, ()) _ hm
                (by dsimp only; omega) hcore3 hs3'
                ⟨by rw [hoff1]; exact htot_le, by rw [hl1]; omega, ⟨hpres3.1, hpres3.2⟩⟩)
            (fun J3 hJ3 => by
              have hrem : (v25 - off_c).toNat = v25.toNat - off_c.toNat := by
                rw [BitVec.toNat_sub]; omega
              c0_hsplit
              · have htr3 : l.toNat < s2.scratch.tarjan_reach.length := hl_tr
                c0_hsteps
                exact hJ3 (v25 - off_c, ()) _
                  ⟨{ s2 with scratch := { s2.scratch with
                      tarjan_reach := s2.scratch.tarjan_reach.set l.toNat
                        ((v25 - off_c).setWidth 32) } },
                    rfl, m7b_ok_tr hs2, by rw [hrem]; omega, ⟨hpres2.1, hpres2.2⟩, hm⟩
              · have hdeg_le : deg.toNat ≤ v25.toNat - off_c.toNat := by
                  dsimp only [deg] at hc ⊢
                  try rw [m7b_zext32] at hc
                  try rw [show (32 : BitVec 64).toNat = 32 from rfl] at hc
                  try rw [show (5 : BitVec 64).toNat = 5 from rfl] at hc
                  omega
                c0_hsteps
                exact hJ3 (deg.setWidth 64, ()) m2
                  ⟨s2, rfl, hs2, by rw [m7b_zext32]; omega, hpres2, hm2⟩))
        (fun J2 hJ2 => by
          c0_hsplit
          · c0_hsteps; exact hJ2 (v25, ()) m2 ⟨rfl, Nat.le_refl _⟩
          · c0_hsteps; exact hJ2 (off, ()) m2 ⟨rfl, hoff_le⟩)
    · -- Pass 2 done (`l ≥ 2 * cur_vars`): enter Pass 3 (`J2`: `ci < ncl`)
      c0_hsteps_nogrp
      refine wp_loop_safety_slice_pure (fullSafetySlice c) s2 R
        (fun s3 (ci, ()) => ci.toNat ≤ ncl.toNat ∧ FullExtScratchPres s s3)
        (fun (ci, ()) => ncl.toNat - ci.toNat)
        (fun J2 hJ2 => by
          c0_hsteps; exact hJ2 s2 (0#64, ()) m2 hm2 rfl hs2 ⟨Nat.zero_le _, hpres2⟩)
        (fun J2 s3 (ci, ()) m3 hcore3 hs3 ⟨hci_le, hpres3⟩ hm3 hJ2 => ?_)
      dsimp only [fullSafetySlice] at hs3 hm3
      have hceq3 : s3.core = s.core := Eq.trans hcore3 hceq2
      c0_hsplit
      · have hci_lt : ci.toNat < ncl.toNat := by exact hc
        have hi0_eq := m7b_bv64_32_add_2n (n := ci) (by omega)
        have hi1_eq := m7b_bv64_32_add_2n1 (n := ci) (by omega)
        have hsbl3 := hs3.scratch_ok.scratch_buf_len
        have hi0_sb : (32#64 + (ci <<< (1 : Nat))).toNat < s3.scratch.scratch_buf.length := by
          rw [hi0_eq, hsbl3]; omega
        have hi1_sb : (32#64 + (ci <<< (1 : Nat)) + 1#64).toNat <
            s3.scratch.scratch_buf.length := by
          rw [hi1_eq, hsbl3]; omega
        c0_hsteps_nogrp
        let e0 := s3.scratch.scratch_buf[(32#64 + (ci <<< (1 : Nat))).toNat]'hi0_sb
        let e1 := s3.scratch.scratch_buf[(32#64 + (ci <<< (1 : Nat)) + 1#64).toNat]'hi1_sb
        have he0_def : s3.scratch.scratch_buf[(BitVec.toNat (32 : BitVec 64) +
            2 * ci.toNat) % 2 ^ 64]'(by
              rw [show BitVec.toNat (32 : BitVec 64) = 32 from rfl,
                Nat.mod_eq_of_lt (by omega : 32 + 2 * ci.toNat < 2 ^ 64), hsbl3]; omega) =
            e0 := by
          dsimp only [e0]; congr 1
          rw [hi0_eq, show BitVec.toNat (32 : BitVec 64) = 32 from rfl,
            Nat.mod_eq_of_lt (by omega)]
        have he1_def : s3.scratch.scratch_buf[(BitVec.toNat (32 : BitVec 64) +
            2 * ci.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
              rw [show BitVec.toNat (32 : BitVec 64) = 32 from rfl,
                show BitVec.toNat (1 : BitVec 64) = 1 from rfl,
                Nat.mod_eq_of_lt (by omega : 32 + 2 * ci.toNat + 1 < 2 ^ 64), hsbl3]; omega) =
            e1 := by
          dsimp only [e1]; congr 1
          rw [hi1_eq, show BitVec.toNat (32 : BitVec 64) = 32 from rfl,
            show BitVec.toNat (1 : BitVec 64) = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
        refine wp_join_group (ts := [])
          (fun () m4 => ∃ s4 : FullState,
            PreservesCoreSlice FullState.core s3 s4 ∧ s4.LengthsOk c ∧
            FullExtScratchPres s s4 ∧ (FullMem c s4 ⋆ R) m4)
          (fun _ _ m4 ⟨s4, hcore4, hs4, hpres4, hm4⟩ => by
            have hci1 : (ci + 1#64).toNat = ci.toNat + 1 := m7b_bv64_add1_toNat (by omega)
            c0_hsteps
            exact hJ2 s4 (ci + 1#64, ()) m4 hm4 (by dsimp only; omega) hcore4 hs4
              ⟨by rw [hci1]; omega, hpres4⟩)
          (fun J3 hJ3 => ?_)
        c0_hsplit
        · -- Pass 3 binary (`e0 & 0x80000000 != 0`)
          let la := e0 &&& 0x7FFFFFFF#32
          refine wp_join_group (ts := [])
            (fun () m4 => ∃ s4 : FullState,
              PreservesCoreSlice FullState.core s3 s4 ∧ s4.LengthsOk c ∧
              FullExtScratchPres s s4 ∧ (FullMem c s4 ⋆ R) m4)
            (fun _ _ m4 ⟨s4, hcore4, hs4, hpres4, hm4⟩ => by
              have hceq4 : s4.core = s.core := Eq.trans hcore4 hceq3
              refine wp_join_group (ts := [])
                (fun () m5 => ∃ s5 : FullState,
                  PreservesCoreSlice FullState.core s4 s5 ∧ s5.LengthsOk c ∧
                  FullExtScratchPres s s5 ∧ (FullMem c s5 ⋆ R) m5)
                (fun _ _ m5 ⟨s5, hcore5, hs5, hpres5, hm5⟩ => by
                  c0_hsteps; exact hJ3 () m5 ⟨s5, Eq.trans hcore5 hcore4, hs5, hpres5, hm5⟩)
                (fun J5 hJ5 => by
                  c0_hsplit
                  · have he1_lt : e1.toNat < 2 * s.core.cur_vars := by
                      rw [he1_def] at hc
                      try rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc
                      try rw [Nat.mod_eq_of_lt (by omega : 2 * s.core.cur_vars < 2 ^ 64)] at hc
                      exact hc
                    have he1_v : (e1.setWidth 64).toNat < s4.core.vals.length := by
                      rw [m7b_zext32, hceq4, hvl]; omega
                    c0_hsplit
                    · have he1_ws1 : (e1.setWidth 64).toNat < s4.scratch.wsort.length := by
                        rw [m7b_zext32, hs4.scratch_ok.wsort_len]; omega
                      have he1_tmk : (e1.setWidth 64).toNat < s4.scratch.tarjan_mark.length := by
                        rw [m7b_zext32, hs4.scratch_ok.tarjan_mark_len]; omega
                      have he1_tr : (e1.setWidth 64).toNat < s4.scratch.tarjan_reach.length := by
                        rw [m7b_zext32, hs4.scratch_ok.tarjan_reach_len]; omega
                      c0_hsteps_nogrp
                      let cur := (s4.scratch.wsort[(e1.setWidth 64).toNat]'he1_ws1).setWidth 64
                      refine wp_join_group (ts := [])
                        (fun () m5 => ∃ s5 : FullState,
                          PreservesCoreSlice FullState.core s4 s5 ∧ s5.LengthsOk c ∧
                          FullExtScratchPres s s5 ∧ (FullMem c s5 ⋆ R) m5)
                        (fun _ _ m5 h => by c0_hsteps; exact hJ5 () m5 h)
                        (fun J6 hJ6 => by
                          c0_hsplit
                          · c0_hsplit
                            · have hcur_32 : cur.toNat < 2 ^ 32 := by
                                dsimp only [cur]; rw [m7b_zext32]
                                exact (s4.scratch.wsort[(e1.setWidth 64).toNat]'he1_ws1).isLt
                              have hcur_sb : (v24 + cur).toNat <
                                  s4.scratch.scratch_buf.length := by
                                rw [m7b_bv64_add2_toNat (by rw [hv24]; omega),
                                  hs4.scratch_ok.scratch_buf_len]
                                have hcur_def : s4.scratch.wsort[e1.toNat]'(by
                                    rw [hs4.scratch_ok.wsort_len]; omega) =
                                    s4.scratch.wsort[(e1.setWidth 64).toNat]'he1_ws1 := by
                                  congr 1
                                simp only [he1_def] at hc
                                try simp only [hcur_def] at hc
                                dsimp only [cur]; rw [m7b_zext32]
                                try rw [show (32 : BitVec 64).toNat = 32 from rfl] at hc
                                omega
                              c0_hsteps
                              let s5 : FullState := { s4 with scratch := { s4.scratch with
                                scratch_buf := s4.scratch.scratch_buf.set (v24 + cur).toNat
                                  (ci.setWidth 32)
                                wsort := s4.scratch.wsort.set (e1.setWidth 64).toNat
                                  ((cur + 1#64).setWidth 32) } }
                              exact hJ6 () _
                                ⟨s5, rfl, m7b_ok_wsort (m7b_len_scrBuf hs4),
                                  ⟨hpres4.1, hpres4.2⟩, hm⟩
                            · c0_hsteps; exact hJ6 () m4 ⟨s4, rfl, hs4, hpres4, hm4⟩
                          · c0_hsteps; exact hJ6 () m4 ⟨s4, rfl, hs4, hpres4, hm4⟩)
                    · c0_hsteps; exact hJ5 () m4 ⟨s4, rfl, hs4, hpres4, hm4⟩
                  · c0_hsteps; exact hJ5 () m4 ⟨s4, rfl, hs4, hpres4, hm4⟩))
            (fun J4 hJ4 => by
              c0_hsplit
              · have hla_lt : la.toNat < 2 * s.core.cur_vars := by
                  rw [he0_def] at hc; dsimp only [la]
                  try rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc
                  try rw [Nat.mod_eq_of_lt (by omega : 2 * s.core.cur_vars < 2 ^ 64)] at hc
                  exact hc
                have hla_v : (la.setWidth 64).toNat < s3.core.vals.length := by
                  rw [m7b_zext32, hceq3, hvl]; omega
                c0_hsplit
                · have hla_ws1 : (la.setWidth 64).toNat < s3.scratch.wsort.length := by
                    rw [m7b_zext32, hs3.scratch_ok.wsort_len]; omega
                  have hla_tmk : (la.setWidth 64).toNat < s3.scratch.tarjan_mark.length := by
                    rw [m7b_zext32, hs3.scratch_ok.tarjan_mark_len]; omega
                  have hla_tr : (la.setWidth 64).toNat < s3.scratch.tarjan_reach.length := by
                    rw [m7b_zext32, hs3.scratch_ok.tarjan_reach_len]; omega
                  c0_hsteps_nogrp
                  let cur := (s3.scratch.wsort[(la.setWidth 64).toNat]'hla_ws1).setWidth 64
                  refine wp_join_group (ts := [])
                    (fun () m4 => ∃ s4 : FullState,
                      PreservesCoreSlice FullState.core s3 s4 ∧ s4.LengthsOk c ∧
                      FullExtScratchPres s s4 ∧ (FullMem c s4 ⋆ R) m4)
                    (fun _ _ m4 h => by c0_hsteps; exact hJ4 () m4 h)
                    (fun J5 hJ5 => by
                      c0_hsplit
                      · c0_hsplit
                        · have hcur_32 : cur.toNat < 2 ^ 32 := by
                            dsimp only [cur]; rw [m7b_zext32]
                            exact (s3.scratch.wsort[(la.setWidth 64).toNat]'hla_ws1).isLt
                          have hcur_sb : (v24 + cur).toNat < s3.scratch.scratch_buf.length := by
                            rw [m7b_bv64_add2_toNat (by rw [hv24]; omega),
                              hs3.scratch_ok.scratch_buf_len]
                            have him2 : (2147483647 : BitVec 32) = 0x7FFFFFFF#32 := rfl
                            have hcur_def : s3.scratch.wsort[(e0 &&& 0x7FFFFFFF#32).toNat]'(by
                                rw [hs3.scratch_ok.wsort_len]; dsimp only [la] at hla_lt; omega) =
                                s3.scratch.wsort[(la.setWidth 64).toNat]'hla_ws1 := by
                              congr 1
                            simp only [he0_def] at hc
                            dsimp only [lift2, Arg.val] at hc
                            simp only [him2] at hc
                            simp only [hcur_def] at hc
                            dsimp only [cur]; rw [m7b_zext32]
                            try rw [show (32 : BitVec 64).toNat = 32 from rfl] at hc
                            omega
                          c0_hsteps
                          let s4 : FullState := { s3 with scratch := { s3.scratch with
                            scratch_buf := s3.scratch.scratch_buf.set (v24 + cur).toNat
                              (ci.setWidth 32)
                            wsort := s3.scratch.wsort.set (la.setWidth 64).toNat
                              ((cur + 1#64).setWidth 32) } }
                          exact hJ5 () _
                            ⟨s4, rfl, m7b_ok_wsort (m7b_len_scrBuf hs3),
                              ⟨hpres3.1, hpres3.2⟩, hm⟩
                        · c0_hsteps; exact hJ5 () m3 ⟨s3, rfl, hs3, hpres3, hm3⟩
                      · c0_hsteps; exact hJ5 () m3 ⟨s3, rfl, hs3, hpres3, hm3⟩)
                · c0_hsteps; exact hJ4 () m3 ⟨s3, rfl, hs3, hpres3, hm3⟩
              · c0_hsteps; exact hJ4 () m3 ⟨s3, rfl, hs3, hpres3, hm3⟩)
        · -- Pass 3 large (`e0 & 0x80000000 == 0`)
          refine wp_join_group (ts := [])
            (fun () m4 => ∃ s4 : FullState,
              PreservesCoreSlice FullState.core s3 s4 ∧ s4.LengthsOk c ∧
              FullExtScratchPres s s4 ∧ (FullMem c s4 ⋆ R) m4)
            (fun _ _ m4 h => by c0_hsteps; exact hJ3 () m4 h)
            (fun J4 hJ4 => ?_)
          c0_hsplit
          · have he0_3 : e0.toNat + 3 ≤ s.core.arena_len := by
              rw [he0_def] at hc
              try rw [show (3 : BitVec 64).toNat = 3 from rfl] at hc
              try rw [Nat.mod_eq_of_lt (by have := e0.isLt; omega)] at hc
              try rw [Nat.mod_eq_of_lt (by omega : s.core.arena_len < 2 ^ 64)] at hc
              exact hc
            have he02_ar : (e0.setWidth 64 + 2#64).toNat < s3.core.arena.length := by
              rw [BitVec.toNat_add, m7b_zext32, show (2#64 : BitVec 64).toNat = 2 from rfl,
                Nat.mod_eq_of_lt (by omega), hceq3, harl]; omega
            c0_hsteps_nogrp
            let sz := s3.core.arena[(e0.setWidth 64 + 2#64).toNat]'he02_ar
            have hsz_def : s3.core.arena[(e0.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by
                rw [show BitVec.toNat (2 : BitVec 64) = 2 from rfl,
                  Nat.mod_eq_of_lt (by omega : e0.toNat + 2 < 2 ^ 64), hceq3, harl]
                omega) = sz := by
              dsimp only [sz]; congr 1
            refine wp_join_group (ts := [])
              (fun () m4 => ∃ s4 : FullState,
                PreservesCoreSlice FullState.core s3 s4 ∧ s4.LengthsOk c ∧
                FullExtScratchPres s s4 ∧ (FullMem c s4 ⋆ R) m4)
              (fun _ _ m4 h => by c0_hsteps; exact hJ4 () m4 h)
              (fun J5 hJ5 => ?_)
            c0_hsplit
            · c0_hsplit
              · have he0sz : e0.toNat + 3 + sz.toNat ≤ s.core.arena_len := by
                  simp only [he0_def, hsz_def] at hc
                  try rw [show (3 : BitVec 64).toNat = 3 from rfl] at hc
                  try rw [Nat.mod_eq_of_lt (by omega : e0.toNat + 3 < 2 ^ 64)] at hc
                  try rw [Nat.mod_eq_of_lt (by have := sz.isLt; omega)] at hc
                  try rw [Nat.mod_eq_of_lt (by omega : s.core.arena_len < 2 ^ 64)] at hc
                  exact hc
                c0_hsteps_nogrp
                refine wp_loop_safety_slice_pure (fullSafetySlice c) s3 R
                  (fun sK (k, ()) => k.toNat ≤ sz.toNat ∧ FullExtScratchPres s sK)
                  (fun (k, ()) => sz.toNat - k.toNat)
                  (fun J6 hJ6 => by
                    c0_hsteps; exact hJ6 s3 (0#32, ()) m3 hm3 rfl hs3
                      ⟨Nat.zero_le _, hpres3⟩)
                  (fun J6 sK (k, ()) mK hcoreK hsK ⟨hk_le, hpresK⟩ hmK hJ6 => ?_)
                dsimp only [fullSafetySlice] at hsK hmK
                have hceqK : sK.core = s.core := Eq.trans hcoreK hceq3
                c0_hsplit
                · have hk_lt : k.toNat < sz.toNat := by simp only [he0_def, hsz_def] at hc; exact hc
                  have hk1 : (k + 1#32).toNat = k.toNat + 1 := m7b_bv32_add1_lt hk_lt
                  have hl_ar : (e0.setWidth 64 + 3#64 + k.setWidth 64).toNat <
                      sK.core.arena.length := by
                    rw [BitVec.toNat_add, BitVec.toNat_add, m7b_zext32, m7b_zext32,
                      show (3#64 : BitVec 64).toNat = 3 from rfl,
                      Nat.mod_eq_of_lt (by omega : e0.toNat + 3 < 2 ^ 64),
                      Nat.mod_eq_of_lt (by omega : e0.toNat + 3 + k.toNat < 2 ^ 64),
                      hceqK, harl]; omega
                  c0_hsteps_nogrp
                  let lit := sK.core.arena[(e0.setWidth 64 + 3#64 + k.setWidth 64).toNat]'hl_ar
                  refine wp_join_group (ts := [])
                    (fun () mN => ∃ sN : FullState,
                      PreservesCoreSlice FullState.core sK sN ∧ sN.LengthsOk c ∧
                      FullExtScratchPres s sN ∧ (FullMem c sN ⋆ R) mN)
                    (fun _ _ mN ⟨sN, hcoreN, hsN, hpresN, hmN⟩ => by
                      c0_hsteps
                      exact hJ6 sN (k + 1#32, ()) mN hmN (by dsimp only; rw [hk1]; omega)
                        hcoreN hsN ⟨by rw [hk1]; omega, hpresN⟩)
                    (fun J7 hJ7 => by
                      have hlit_def : sK.core.arena[(e0.toNat + BitVec.toNat (3 : BitVec 64) +
                          k.toNat) % 2 ^ 64]'(by
                            rw [show BitVec.toNat (3 : BitVec 64) = 3 from rfl,
                              Nat.mod_eq_of_lt (by omega : e0.toNat + 3 + k.toNat < 2 ^ 64),
                              hceqK, harl]; omega) = lit := by
                        dsimp only [lit]; congr 1
                        rw [BitVec.toNat_add, BitVec.toNat_add, m7b_zext32, m7b_zext32,
                          show BitVec.toNat (3 : BitVec 64) = 3 from rfl,
                          show (3#64 : BitVec 64).toNat = 3 from rfl,
                          Nat.mod_eq_of_lt (by omega : e0.toNat + 3 < 2 ^ 64)]
                      c0_hsplit
                      · have hlit_lt : lit.toNat < 2 * s.core.cur_vars := by
                          simp only [he0_def, hlit_def] at hc
                          try rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc
                          try rw [Nat.mod_eq_of_lt (by omega : 2 * s.core.cur_vars < 2 ^ 64)] at hc
                          exact hc
                        have hlit_v : (lit.setWidth 64).toNat < sK.core.vals.length := by
                          rw [m7b_zext32, hceqK, hvl]; omega
                        c0_hsplit
                        · have hlit_ws1 : (lit.setWidth 64).toNat <
                              sK.scratch.wsort.length := by
                            rw [m7b_zext32, hsK.scratch_ok.wsort_len]; omega
                          have hlit_tmk : (lit.setWidth 64).toNat <
                              sK.scratch.tarjan_mark.length := by
                            rw [m7b_zext32, hsK.scratch_ok.tarjan_mark_len]; omega
                          have hlit_tr : (lit.setWidth 64).toNat <
                              sK.scratch.tarjan_reach.length := by
                            rw [m7b_zext32, hsK.scratch_ok.tarjan_reach_len]; omega
                          c0_hsteps_nogrp
                          let cur :=
                            (sK.scratch.wsort[(lit.setWidth 64).toNat]'hlit_ws1).setWidth 64
                          refine wp_join_group (ts := [])
                            (fun () mN => ∃ sN : FullState,
                              PreservesCoreSlice FullState.core sK sN ∧ sN.LengthsOk c ∧
                              FullExtScratchPres s sN ∧ (FullMem c sN ⋆ R) mN)
                            (fun _ _ mN h => by c0_hsteps; exact hJ7 () mN h)
                            (fun J8 hJ8 => by
                              c0_hsplit
                              · c0_hsplit
                                · have hcur_32 : cur.toNat < 2 ^ 32 := by
                                    dsimp only [cur]; rw [m7b_zext32]
                                    exact
                                      (sK.scratch.wsort[(lit.setWidth 64).toNat]'hlit_ws1).isLt
                                  have hcur_sb : (v24 + cur).toNat <
                                      sK.scratch.scratch_buf.length := by
                                    rw [m7b_bv64_add2_toNat (by rw [hv24]; omega),
                                      hsK.scratch_ok.scratch_buf_len]
                                    have hcur_def : sK.scratch.wsort[lit.toNat]'(by
                                        rw [hsK.scratch_ok.wsort_len]; omega) =
                                        sK.scratch.wsort[(lit.setWidth 64).toNat]'hlit_ws1 := by
                                      congr 1; try rw [m7b_zext32]
                                    simp only [he0_def, hlit_def] at hc
                                    try simp only [hcur_def] at hc
                                    dsimp only [cur]; rw [m7b_zext32]
                                    try rw [show (32 : BitVec 64).toNat = 32 from rfl] at hc
                                    omega
                                  c0_hsteps
                                  let sN : FullState := { sK with scratch := { sK.scratch with
                                    scratch_buf := sK.scratch.scratch_buf.set (v24 + cur).toNat
                                      (ci.setWidth 32)
                                    wsort := sK.scratch.wsort.set (lit.setWidth 64).toNat
                                      ((cur + 1#64).setWidth 32) } }
                                  exact hJ8 () _
                                    ⟨sN, rfl, m7b_ok_wsort (m7b_len_scrBuf hsK),
                                      ⟨hpresK.1, hpresK.2⟩, hm⟩
                                · c0_hsteps; exact hJ8 () mK ⟨sK, rfl, hsK, hpresK, hmK⟩
                              · c0_hsteps; exact hJ8 () mK ⟨sK, rfl, hsK, hpresK, hmK⟩)
                        · c0_hsteps; exact hJ7 () mK ⟨sK, rfl, hsK, hpresK, hmK⟩
                      · c0_hsteps; exact hJ7 () mK ⟨sK, rfl, hsK, hpresK, hmK⟩)
                · c0_hsteps; exact hJ5 () mK ⟨sK, hcoreK, hsK, hpresK, hmK⟩
              · c0_hsteps; exact hJ5 () m3 ⟨s3, rfl, hs3, hpres3, hm3⟩
            · c0_hsteps; exact hJ5 () m3 ⟨s3, rfl, hs3, hpres3, hm3⟩
          · c0_hsteps; exact hJ4 () m3 ⟨s3, rfl, hs3, hpres3, hm3⟩
      · -- All 3 passes done: `ret ulen`
        c0_hsteps
        exact hQ (ulen, ()) s3 m3 hceq3 hs3 ⟨hpres3, hulen_le⟩ hm3

private theorem m7b_rng_call {rs : List Ty} {Γ : Env} {Q : Post rs} {X : XPost} {m : Mem 64}
    (hRng : ∀ a m Q X, Full.fullRngNextSpec a m Q X →
      Γ "full_rng_next" [i64] [i64] a m Q X)
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont rs}
    (hh : args.fst.val = c.hdr) (hm : (FullMem c s ⋆ R) m) (hs : s.LengthsOk c)
    (hk : ∀ (r : Val i64) (s' : FullState) (m' : Mem 64),
      s'.core = s.core → s'.LengthsOk c →
      s'.scratch = { s.scratch with rng_state := s'.scratch.rng_state } →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (Expr.call "full_rng_next" args k) m :=
  wp_call_of_spec args k (hRng (vals args) m (fun r m' => wp Γ Q X (k r) m') X
    ⟨c, s, R, hh, hs, hm, fun _ s' m' hcore hs' hsc hm' => hk _ s' m' hcore hs' hsc hm'⟩)

private theorem m7b_bv64_shl1_32 (x : BitVec 32) :
    (x.setWidth 64 <<< 1).toNat = 2 * x.toNat := by
  have hx : x.toNat < 2 ^ 32 := x.isLt
  rw [BitVec.toNat_shiftLeft, m7b_zext32, Nat.shiftLeft_eq, Nat.pow_one,
    Nat.mod_eq_of_lt (by omega : x.toNat * 2 < 2 ^ 64)]
  omega

private theorem m7b_bv64_ne_zero_of_pos {x : BitVec 64} (h : 0 < x.toNat) : x ≠ 0#64 := by
  intro heq; subst heq; simp at h

private theorem m7b_bv64_add1_lt {x : BitVec 64} {n : Nat} (h : x.toNat < n) (hn : n < 2 ^ 64) :
    (x + 1#64).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl,
    Nat.mod_eq_of_lt (by omega : x.toNat + 1 < 2 ^ 64)]

/-- WP proof for `full_walk_pick_m7` (`m7PickSpec`). -/
theorem full_walk_pick_m7_wp (Γ : Env)
    (hBrk : ∀ a m Q X, m7BreakSpec a m Q X →
      Γ "full_walk_break_m7" [i64, i32, i64] [i32] a m Q X)
    (hRng : ∀ a m Q X, Full.fullRngNextSpec a m Q X →
      Γ "full_rng_next" [i64] [i64] a m Q X)
    (a : Tup Val [i64, i32, i64]) (m : Mem 64) (Q : Post [i64]) (X : XPost)
    (hS : m7PickSpec a m Q X) :
    Func.wp Γ full_walk_pick_m7_body a m Q X := by
  rcases a with ⟨h, cl, ncl, ⟨⟩⟩
  rw [m7PickSpec_eq] at hS
  rcases hS with ⟨c, s, R, hh, hlen, hm, hQ⟩
  dsimp only [Func.wp, full_walk_pick_m7_body]
  dsimp only [fullSafetySlice] at hlen hm
  subst hh
  have hdb : LratBytes.dimacsBound = 2 ^ 28 := rfl
  have hmax := c.hmaxv; have haca := c.harena; have hwc := c.hwcap; have hscr := c.hscr
  have hcv_le := hlen.core_ok.cur_vars_le
  have harl := hlen.core_ok.arena_len_arr; have hale := hlen.core_ok.arena_len_le
  have hvl := hlen.core_ok.vals_len; have hsbl := hlen.scratch_ok.scratch_buf_len
  have htrl := hlen.scratch_ok.tarjan_reach_len
  have hws1 := hlen.scratch_ok.work_stk1_len; have hws2 := hlen.scratch_ok.work_stk2_len
  c0_hsplit
  · c0_hsteps; exact hQ (0xffffffff#64, ()) s m rfl hlen ⟨rfl, rfl⟩ hm
  have hcv_pos : 0 < s.core.cur_vars := Nat.pos_of_ne_zero fun h0 => hc (BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)]; exact h0))
  c0_hsplit
  · c0_hsteps; exact hQ (0xffffffff#64, ()) s m rfl hlen ⟨rfl, rfl⟩ hm
  have hcv_ok : s.core.cur_vars ≤ c.max_vars := hcv_le
  have hmax_pos : 0 < c.max_vars := by omega
  c0_hsplit
  · c0_hsteps; exact hQ (0xffffffff#64, ()) s m rfl hlen ⟨rfl, rfl⟩ hm
  have hncl_pos : 0 < ncl.toNat := Nat.pos_of_ne_zero fun h0 => hc (BitVec.eq_of_toNat_eq h0)
  c0_hsplit
  · c0_hsteps; exact hQ (0xffffffff#64, ()) s m rfl hlen ⟨rfl, rfl⟩ hm
  have hcl_lt : cl.toNat < ncl.toNat := Nat.lt_of_not_le hc
  c0_hsplit
  · c0_hsteps; exact hQ (0xffffffff#64, ()) s m rfl hlen ⟨rfl, rfl⟩ hm
  have hncl_le : ncl.toNat ≤ c.scratch_cap := by
    rw [Nat.mod_eq_of_lt (by omega : c.scratch_cap < 2 ^ 64)] at hc
    exact Nat.le_of_not_lt hc
  c0_hsplit
  · c0_hsteps; exact hQ (0xffffffff#64, ()) s m rfl hlen ⟨rfl, rfl⟩ hm
  have hcap_ok : 32 + 5 * ncl.toNat ≤ c.scratch_cap := by
    rw [show (32 : BitVec 64).toNat = 32 from rfl, show (5 : BitVec 64).toNat = 5 from rfl,
      Nat.mod_eq_of_lt (by omega : c.scratch_cap < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : 32 + 5 * ncl.toNat < 2 ^ 64)] at hc
    exact Nat.le_of_not_lt hc
  have hi0_eq : (32#64 + cl.setWidth 64 <<< 1).toNat = 32 + 2 * cl.toNat := by
    rw [BitVec.toNat_add, m7b_bv64_shl1_32, show (32#64 : BitVec 64).toNat = 32 from rfl,
      Nat.mod_eq_of_lt (by omega)]
  have hi1_eq : (32#64 + cl.setWidth 64 <<< 1 + 1#64).toNat = 32 + 2 * cl.toNat + 1 := by
    rw [BitVec.toNat_add, hi0_eq, show (1#64 : BitVec 64).toNat = 1 from rfl,
      Nat.mod_eq_of_lt (by omega)]
  have hi0_sb : (32#64 + cl.setWidth 64 <<< 1).toNat < s.scratch.scratch_buf.length := by
    rw [hi0_eq, hsbl]; omega
  have hi1_sb : (32#64 + cl.setWidth 64 <<< 1 + 1#64).toNat < s.scratch.scratch_buf.length := by
    rw [hi1_eq, hsbl]; omega
  have h2cv_eq : (BitVec.ofNat 64 s.core.cur_vars <<< 1).toNat = 2 * s.core.cur_vars := by
    rw [BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars * 2 < 2 ^ 64)]; omega
  c0_hsteps_nogrp
  let e0 := s.scratch.scratch_buf[(32#64 + cl.setWidth 64 <<< 1).toNat]'hi0_sb
  let e1 := s.scratch.scratch_buf[(32#64 + cl.setWidth 64 <<< 1 + 1#64).toNat]'hi1_sb
  have he0_def : s.scratch.scratch_buf[(BitVec.toNat (32 : BitVec 64) + 2 * cl.toNat) %
      2 ^ 64]'(by
      rw [show BitVec.toNat (32 : BitVec 64) = 32 from rfl,
        Nat.mod_eq_of_lt (by omega : 32 + 2 * cl.toNat < 2 ^ 64), hsbl]; omega) = e0 := by
    dsimp only [e0]; congr 1
    rw [hi0_eq, show BitVec.toNat (32 : BitVec 64) = 32 from rfl,
      Nat.mod_eq_of_lt (by omega : 32 + 2 * cl.toNat < 2 ^ 64)]
  have he1_def : s.scratch.scratch_buf[(BitVec.toNat (32 : BitVec 64) + 2 * cl.toNat +
      BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
      rw [show BitVec.toNat (32 : BitVec 64) = 32 from rfl,
        show BitVec.toNat (1 : BitVec 64) = 1 from rfl,
        Nat.mod_eq_of_lt (by omega : 32 + 2 * cl.toNat + 1 < 2 ^ 64), hsbl]; omega) = e1 := by
    dsimp only [e1]; congr 1
    rw [hi1_eq, show BitVec.toNat (32 : BitVec 64) = 32 from rfl,
      show BitVec.toNat (1 : BitVec 64) = 1 from rfl,
      Nat.mod_eq_of_lt (by omega : 32 + 2 * cl.toNat + 1 < 2 ^ 64)]
  c0_hsplit
  · -- Binary clause (`e0 &&& 0x80000000 != 0`)
    clear hc
    let a0 := e0 &&& 0x7FFFFFFF#32
    refine wp_join_group (ts := [Ty.bool])
      (fun (fa, ()) m1 => m1 = m ∧ (fa = true → a0.toNat < 2 * s.core.cur_vars))
      (fun _ ⟨fa, ⟨⟩⟩ m1 ⟨hm1, hfa_lt⟩ => ?_)
      (fun J0 hJ0 => by
        c0_hsplit
        · have ha0_lt : a0.toNat < 2 * s.core.cur_vars := by
            simp only [he0_def] at hc
            rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64),
              Nat.mod_eq_of_lt (by omega : 2 * s.core.cur_vars < 2 ^ 64)] at hc
            exact hc
          have ha0_v : (a0.setWidth 64).toNat < s.core.vals.length := by
            rw [m7b_zext32, hvl]; omega
          c0_hsteps_nogrp
          c0_hsplit
          · c0_hsteps; exact hJ0 (true, ()) m ⟨rfl, fun _ => ha0_lt⟩
          · c0_hsteps; exact hJ0 (false, ()) m ⟨rfl, Bool.noConfusion⟩
        · c0_hsteps; exact hJ0 (false, ()) m ⟨rfl, Bool.noConfusion⟩)
    subst m1
    refine wp_join_group (ts := [Ty.bool])
      (fun (fb, ()) m2 => m2 = m ∧ (fb = true → e1.toNat < 2 * s.core.cur_vars))
      (fun _ ⟨fb, ⟨⟩⟩ m2 ⟨hm2, hfb_lt⟩ => ?_)
      (fun J1 hJ1 => by
        c0_hsplit
        · have he1_lt : e1.toNat < 2 * s.core.cur_vars := by
            simp only [he1_def] at hc
            rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64),
              Nat.mod_eq_of_lt (by omega : 2 * s.core.cur_vars < 2 ^ 64)] at hc
            exact hc
          have he1_v : (e1.setWidth 64).toNat < s.core.vals.length := by
            rw [m7b_zext32, hvl]; omega
          c0_hsteps_nogrp
          c0_hsplit
          · c0_hsteps; exact hJ1 (true, ()) m ⟨rfl, fun _ => he1_lt⟩
          · c0_hsteps; exact hJ1 (false, ()) m ⟨rfl, Bool.noConfusion⟩
        · c0_hsteps; exact hJ1 (false, ()) m ⟨rfl, Bool.noConfusion⟩)
    subst m2
    refine wp_join_group (ts := [])
      (fun () m3 => m3 = m ∧ (fa = true ∨ fb = true))
      (fun _ _ m3 ⟨hm3, hor⟩ => ?_)
      (fun J2 hJ2 => by
        c0_hsplit
        · c0_hsteps; exact hJ2 () m ⟨rfl, Or.inl (by assumption)⟩
        · c0_hsplit
          · c0_hsteps; exact hJ2 () m ⟨rfl, Or.inr (by assumption)⟩
          · c0_hsteps; exact hQ (0xffffffff#64, ()) s m rfl hlen ⟨rfl, rfl⟩ hm)
    subst m3
    refine wp_join_group (ts := [])
      (fun () m4 => m4 = m ∧ fb = true)
      (fun _ _ m4 ⟨hm4, hfb⟩ => ?_)
      (fun J3 hJ3 => by
        c0_hsplit
        · c0_hsplit
          · c0_hsteps; exact hJ3 () m ⟨rfl, by assumption⟩
          · c0_hsteps; exact hQ (a0.setWidth 64, ()) s m rfl hlen ⟨rfl, rfl⟩ hm
        · have hfb : fb = true := by
            rcases hor with ha | hb
            · rw [ha] at hc; cases hc
            · exact hb
          c0_hsteps; exact hJ3 () m ⟨rfl, hfb⟩)
    subst m4
    refine wp_join_group (ts := [])
      (fun () m5 => m5 = m ∧ fa = true)
      (fun _ _ m5 ⟨hm5, hfa⟩ => ?_)
      (fun J4 hJ4 => by
        c0_hsplit
        · c0_hsteps; exact hJ4 () m ⟨rfl, by assumption⟩
        · c0_hsplit
          · c0_hsteps; exact hQ (e1.setWidth 64, ()) s m rfl hlen ⟨rfl, rfl⟩ hm
          · rw [hfb] at *; contradiction)
    subst m5
    have ha0_lt : a0.toNat < 2 * s.core.cur_vars := hfa_lt hfa
    have he1_lt : e1.toNat < 2 * s.core.cur_vars := hfb_lt hfb
    have ha0x_lt : (a0 ^^^ 1#32).toNat < 2 * s.core.cur_vars := m7b_bv32_xor1_lt ha0_lt
    have he1x_lt : (e1 ^^^ 1#32).toNat < 2 * s.core.cur_vars := m7b_bv32_xor1_lt he1_lt
    c0_hsteps_nogrp
    refine m7Break_call hBrk rfl hlen hm fun ba m6 hm6 => ?_
    c0_hsteps_nogrp
    refine m7Break_call hBrk rfl hlen hm6 fun bb m7 hm7 => ?_
    refine wp_join_group (ts := [i64])
      (fun (ia, ()) m8 => m8 = m7 ∧ ia.toNat < 32)
      (fun _ ⟨ia, ⟨⟩⟩ m8 ⟨hm8, hia⟩ => ?_)
      (fun J5 hJ5 => by
        c0_hsplit
        · c0_hsteps
          have hba_lt : (ba.setWidth 64).toNat < 32 := by
            rw [m7b_zext32]; exact Nat.lt_trans hc (by decide)
          exact hJ5 (ba.setWidth 64, ()) m7 ⟨rfl, hba_lt⟩
        · c0_hsteps; exact hJ5 (31#64, ()) m7 ⟨rfl, by decide⟩)
    subst m8
    have hia_sb : ia.toNat < s.scratch.scratch_buf.length := by rw [hsbl]; omega
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64])
      (fun (ib, ()) m9 => m9 = m7 ∧ ib.toNat < 32)
      (fun _ ⟨ib, ⟨⟩⟩ m9 ⟨hm9, hib⟩ => ?_)
      (fun J6 hJ6 => by
        c0_hsplit
        · c0_hsteps
          have hbb_lt : (bb.setWidth 64).toNat < 32 := by
            rw [m7b_zext32]; exact Nat.lt_trans hc (by decide)
          exact hJ6 (bb.setWidth 64, ()) m7 ⟨rfl, hbb_lt⟩
        · c0_hsteps; exact hJ6 (31#64, ()) m7 ⟨rfl, by decide⟩)
    subst m9
    have hib_sb : ib.toNat < s.scratch.scratch_buf.length := by rw [hsbl]; omega
    c0_hsteps_nogrp
    let va := (s.scratch.scratch_buf[ia.toNat]'hia_sb).setWidth 64
    let vb := (s.scratch.scratch_buf[ib.toNat]'hib_sb).setWidth 64
    refine wp_join_group (ts := [i64])
      (fun (sa, ()) ma => ma = m7 ∧ 1 ≤ sa.toNat ∧ sa.toNat < 2 ^ 32)
      (fun _ ⟨sa, ⟨⟩⟩ ma ⟨hma, hsa1, hsa32⟩ => ?_)
      (fun J7 hJ7 => by
        c0_hsplit
        · c0_hsteps; exact hJ7 (1#64, ()) m7 ⟨rfl, by decide, by decide⟩
        · have hva_pos : 1 ≤ va.toNat :=
            Nat.pos_of_ne_zero fun h0 => hc (BitVec.eq_of_toNat_eq h0)
          have hva_32 : va.toNat < 2 ^ 32 := by
            dsimp only [va]; rw [m7b_zext32]; exact BitVec.isLt _
          c0_hsteps; exact hJ7 (va, ()) m7 ⟨rfl, hva_pos, hva_32⟩)
    subst ma
    refine wp_join_group (ts := [i64])
      (fun (sb, ()) mb => mb = m7 ∧ 1 ≤ sb.toNat ∧ sb.toNat < 2 ^ 32)
      (fun _ ⟨sb, ⟨⟩⟩ mb ⟨hmb, hsb1, hsb32⟩ => ?_)
      (fun J8 hJ8 => by
        c0_hsplit
        · c0_hsteps; exact hJ8 (1#64, ()) m7 ⟨rfl, by decide, by decide⟩
        · have hvb_pos : 1 ≤ vb.toNat :=
            Nat.pos_of_ne_zero fun h0 => hc (BitVec.eq_of_toNat_eq h0)
          have hvb_32 : vb.toNat < 2 ^ 32 := by
            dsimp only [vb]; rw [m7b_zext32]; exact BitVec.isLt _
          c0_hsteps; exact hJ8 (vb, ()) m7 ⟨rfl, hvb_pos, hvb_32⟩)
    subst mb
    refine wp_join_group (ts := [i64])
      (fun (sa', ()) mc => mc = m7 ∧ 1 ≤ sa'.toNat ∧ sa'.toNat ≤ 0x40000000)
      (fun _ ⟨sa', ⟨⟩⟩ mc ⟨hmc, hsa'1, hsa'M⟩ => ?_)
      (fun J9 hJ9 => by
        c0_hsplit
        · c0_hsteps; exact hJ9 (0x40000000#64, ()) m7 ⟨rfl, by decide, by decide⟩
        · c0_hsteps; exact hJ9 (sa, ()) m7 ⟨rfl, hsa1, Nat.le_of_not_lt hc⟩)
    subst mc
    refine wp_join_group (ts := [i64])
      (fun (sb', ()) md => md = m7 ∧ 1 ≤ sb'.toNat ∧ sb'.toNat ≤ 0x40000000)
      (fun _ ⟨sb', ⟨⟩⟩ md ⟨hmd, hsb'1, hsb'M⟩ => ?_)
      (fun J10 hJ10 => by
        c0_hsplit
        · c0_hsteps; exact hJ10 (0x40000000#64, ()) m7 ⟨rfl, by decide, by decide⟩
        · c0_hsteps; exact hJ10 (sb, ()) m7 ⟨rfl, hsb1, Nat.le_of_not_lt hc⟩)
    subst md
    have hax_tr : ((a0 ^^^ 1#32).setWidth 64).toNat < s.scratch.tarjan_reach.length := by
      rw [m7b_zext32, htrl]; omega
    have hex_tr : ((e1 ^^^ 1#32).setWidth 64).toNat < s.scratch.tarjan_reach.length := by
      rw [m7b_zext32, htrl]; omega
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64])
      (fun (_, ()) me => me = m7)
      (fun _ ⟨_cnt, ⟨⟩⟩ me hme => ?_)
      (fun J11 hJ11 => by
        c0_hsplit <;> (c0_hsteps; exact hJ11 (_, ()) m7 rfl))
    subst me
    have htot_pos : 0 < (sa' + sb').toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]; omega
    have htot_ne : sa' + sb' ≠ 0#64 := m7b_bv64_ne_zero_of_pos htot_pos
    refine wp_join_group (ts := [i32])
      (fun (_, ()) mf => ∃ s' : FullState,
        s'.core = s.core ∧ s'.LengthsOk c ∧ FullExtScratchPres s s' ∧
        (FullMem c s' ⋆ R) mf)
      (fun _ ⟨_pk, ⟨⟩⟩ mf ⟨s', hc', hs', hpr', hmf⟩ => by
        c0_hsteps; exact hQ _ s' mf hc' hs' hpr' hmf)
      (fun J12 hJ12 => by
        c0_hsteps_nogrp
        refine m7b_rng_call hRng rfl hm7 hlen fun rng s' mf hc' hs' hsc' hmf => ?_
        have hpr' : FullExtScratchPres s s' := by refine ⟨?_, ?_⟩ <;> rw [hsc']
        c0_hsplit
        · c0_hsteps; exact hJ12 (a0, ()) mf ⟨s', hc', hs', hpr', hmf⟩
        · c0_hsteps; exact hJ12 (e1, ()) mf ⟨s', hc', hs', hpr', hmf⟩)
  · c0_hsteps; exact hQ (0xffffffff#64, ()) s m rfl hlen ⟨rfl, rfl⟩ hm
  · c0_hsteps; exact hQ (0xffffffff#64, ()) s m rfl hlen ⟨rfl, rfl⟩ hm
  · c0_hsteps; exact hQ (0xffffffff#64, ()) s m rfl hlen ⟨rfl, rfl⟩ hm
  · -- Large clause (`e0 &&& 0x80000000 == 0`)
    let e0 := s.scratch.scratch_buf[(32#64 + cl.setWidth 64 <<< 1).toNat]'hi0_sb
    have hi0_mod : (BitVec.toNat (32 : BitVec 64) + 2 * cl.toNat) % 2 ^ 64 <
        s.scratch.scratch_buf.length := by
      rw [show BitVec.toNat (32 : BitVec 64) = 32 from rfl,
        Nat.mod_eq_of_lt (by omega : 32 + 2 * cl.toNat < 2 ^ 64), hsbl]; omega
    have he0_def : s.scratch.scratch_buf[(BitVec.toNat (32 : BitVec 64) + 2 * cl.toNat) %
        2 ^ 64]'hi0_mod = e0 := by
      dsimp only [e0]; congr 1
      rw [hi0_eq, show BitVec.toNat (32 : BitVec 64) = 32 from rfl,
        Nat.mod_eq_of_lt (by omega : 32 + 2 * cl.toNat < 2 ^ 64)]
    have he0_3 : e0.toNat + 3 ≤ s.core.arena_len := by
      have hnot3 : ¬s.core.arena_len % 2 ^ 64 <
          ((s.scratch.scratch_buf[(BitVec.toNat (32 : BitVec 64) + 2 * cl.toNat) %
            2 ^ 64]'hi0_mod).toNat + BitVec.toNat (3 : BitVec 64)) % 2 ^ 64 := by assumption
      rw [he0_def, show (3 : BitVec 64).toNat = 3 from rfl,
        show s.core.arena_len % 2 ^ 64 = s.core.arena_len from
          Nat.mod_eq_of_lt (by omega : s.core.arena_len < 2 ^ 64),
        show (e0.toNat + 3) % 2 ^ 64 = e0.toNat + 3 from
          Nat.mod_eq_of_lt (by have := e0.isLt; omega)] at hnot3
      exact Nat.le_of_not_lt hnot3
    have he02_ar : (e0.setWidth 64 + 2#64).toNat < s.core.arena.length := by
      rw [BitVec.toNat_add, m7b_zext32, show (2#64 : BitVec 64).toNat = 2 from rfl,
        Nat.mod_eq_of_lt (by have := e0.isLt; omega), harl]; omega
    let sz := s.core.arena[(e0.setWidth 64 + 2#64).toNat]'he02_ar
    have har2_mod : (e0.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 <
        s.core.arena.length := by
      rw [show BitVec.toNat (2 : BitVec 64) = 2 from rfl,
        Nat.mod_eq_of_lt (by have := e0.isLt; omega), harl]; omega
    have hsz_def : s.core.arena[(e0.toNat + BitVec.toNat (2 : BitVec 64)) %
        2 ^ 64]'har2_mod = sz := by
      dsimp only [sz]
      try (congr 1; try rw [BitVec.toNat_add, m7b_zext32])
    have hsz_ge3 : 3 ≤ sz.toNat := by
      have hlt3 : ¬(s.core.arena[((s.scratch.scratch_buf[(BitVec.toNat (32 : BitVec 64) +
          2 * cl.toNat) % 2 ^ 64]'hi0_mod).toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by
          first | (rw [he0_def]; exact har2_mod) | (rw [← he0_def]; exact har2_mod))).toNat <
          BitVec.toNat (3 : BitVec 32) := by assumption
      have hlt3' : ¬sz.toNat < BitVec.toNat (3 : BitVec 32) := by
        simpa only [he0_def, hsz_def] using hlt3
      exact Nat.le_of_not_lt hlt3'
    have he0sz : e0.toNat + 3 + sz.toNat ≤ s.core.arena_len := by
      simp only [he0_def, hsz_def] at hc
      rw [show (3 : BitVec 64).toNat = 3 from rfl,
        show s.core.arena_len % 2 ^ 64 = s.core.arena_len from
          Nat.mod_eq_of_lt (by omega : s.core.arena_len < 2 ^ 64),
        show (e0.toNat + 3 + sz.toNat) % 2 ^ 64 = e0.toNat + 3 + sz.toNat from
          Nat.mod_eq_of_lt (by have := e0.isLt; have := sz.isLt; omega)] at hc
      exact Nat.le_of_not_lt hc
    clear hc
    refine wp_loop_safety_slice_pure (fullSafetySlice c) s R
      (fun sK (sum_sc, cand_cnt, _fcnt, _tot_brk, fidx, _best, k, ()) =>
        k.toNat ≤ sz.toNat ∧ sum_sc.toNat ≤ k.toNat * 0x40000000 ∧
        cand_cnt.toNat ≤ 2 * c.max_vars ∧ fidx.toNat ≤ sz.toNat ∧ FullExtScratchPres s sK)
      (fun (_, _, _, _, _, _, k, ()) => sz.toNat - k.toNat)
      (fun J0 hJ0 => by
        c0_hsteps
        exact hJ0 s (0#64, 0#64, 0#64, 0#64, sz, 0xffffffff#32, 0#32, ()) m hm rfl hlen
          ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.le_refl _, ⟨rfl, rfl⟩⟩)
      (fun J0 sK (sum_sc, cand_cnt, fcnt, tot_brk, fidx, best, k, ()) mK
          hcoreK hsK ⟨hk_le, hsum_le, hcc_le, hfidx_le, hpresK⟩ hmK hJ0 => by
        dsimp only [fullSafetySlice, PreservesCoreSlice] at hsK hmK hcoreK
        have hceqK : sK.core = s.core := hcoreK
        c0_hsplit
        · have hk_lt : k.toNat < sz.toNat := by simp only [he0_def, hsz_def] at hc; exact hc
          clear hc
          have hk1 : (k + 1#32).toNat = k.toNat + 1 := m7b_bv32_add1_lt hk_lt
          have hl_ar : (e0.setWidth 64 + 3#64 + k.setWidth 64).toNat < sK.core.arena.length := by
            rw [BitVec.toNat_add, BitVec.toNat_add, m7b_zext32, m7b_zext32,
              show (3#64 : BitVec 64).toNat = 3 from rfl,
              Nat.mod_eq_of_lt (by omega : e0.toNat + 3 < 2 ^ 64),
              Nat.mod_eq_of_lt (by omega : e0.toNat + 3 + k.toNat < 2 ^ 64),
              hceqK, harl]; omega
          c0_hsteps_nogrp
          let lit := sK.core.arena[(e0.setWidth 64 + 3#64 + k.setWidth 64).toNat]'hl_ar
          have hlit_def : sK.core.arena[(e0.toNat + BitVec.toNat (3 : BitVec 64) +
              k.toNat) % 2 ^ 64]'(by
              rw [show BitVec.toNat (3 : BitVec 64) = 3 from rfl,
                Nat.mod_eq_of_lt (by omega : e0.toNat + 3 + k.toNat < 2 ^ 64),
                hceqK, harl]; omega) = lit := by
            dsimp only [lit]; congr 1
            rw [BitVec.toNat_add, BitVec.toNat_add, m7b_zext32, m7b_zext32,
              show BitVec.toNat (3 : BitVec 64) = 3 from rfl,
              show (3#64 : BitVec 64).toNat = 3 from rfl,
              Nat.mod_eq_of_lt (by omega : e0.toNat + 3 < 2 ^ 64)]
          refine wp_join_group (ts := [i64, i64, i64, i64, i32, i32])
            (fun (sum_sc', cand_cnt', _, _, fidx', _, ()) mN => ∃ sN : FullState,
              PreservesCoreSlice FullState.core sK sN ∧ sN.LengthsOk c ∧
              sum_sc'.toNat ≤ (k.toNat + 1) * 0x40000000 ∧ cand_cnt'.toNat ≤ 2 * c.max_vars ∧
              fidx'.toNat ≤ sz.toNat ∧ FullExtScratchPres s sN ∧ (FullMem c sN ⋆ R) mN)
            (fun _ ⟨ssc', cc', fc', tb', fi', b', ⟨⟩⟩ mN
                ⟨sN, hcoreN, hsN, hssc', hcc', hfi', hpresN, hmN⟩ => by
              c0_hsteps
              exact hJ0 sN (ssc', cc', fc', tb', fi', b', k + 1#32, ()) mN hmN
                (by dsimp only; rw [hk1]; omega) hcoreN hsN
                ⟨by rw [hk1]; omega, by rw [hk1]; exact hssc', hcc', hfi', hpresN⟩)
            (fun J1 hJ1 => by
              c0_hsplit
              · have hlit_lt : lit.toNat < 2 * s.core.cur_vars := by
                  simp only [he0_def, hlit_def] at hc
                  rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64),
                    Nat.mod_eq_of_lt (by omega : 2 * s.core.cur_vars < 2 ^ 64)] at hc
                  exact hc
                clear hc
                have hlit_v : (lit.setWidth 64).toNat < sK.core.vals.length := by
                  rw [m7b_zext32, hsK.core_ok.vals_len]; omega
                c0_hsteps_nogrp
                c0_hsplit
                · clear hc
                  have hlx_lt : (lit ^^^ 1#32).toNat < 2 * s.core.cur_vars :=
                    m7b_bv32_xor1_lt hlit_lt
                  c0_hsteps_nogrp
                  refine m7Break_call hBrk rfl hsK hmK fun ba mL hmL => ?_
                  refine wp_join_group (ts := [i64])
                    (fun (idx, ()) m1 => m1 = mL ∧ idx.toNat < 32)
                    (fun _ ⟨idx, ⟨⟩⟩ m1 ⟨hm1, hidx⟩ => ?_)
                    (fun J2 hJ2 => by
                      c0_hsplit
                      · c0_hsteps
                        have hba_lt : (ba.setWidth 64).toNat < 32 := by
                          rw [m7b_zext32]; exact Nat.lt_trans hc (by decide)
                        exact hJ2 (ba.setWidth 64, ()) mL ⟨rfl, hba_lt⟩
                      · c0_hsteps; exact hJ2 (31#64, ()) mL ⟨rfl, by decide⟩)
                  subst m1
                  have hidx_sb : idx.toNat < sK.scratch.scratch_buf.length := by
                    rw [hsK.scratch_ok.scratch_buf_len]; omega
                  c0_hsteps_nogrp
                  let raw_sc := sK.scratch.scratch_buf[idx.toNat]'hidx_sb
                  refine wp_join_group (ts := [i32])
                    (fun (sc0, ()) m2 => m2 = mL ∧ 1 ≤ sc0.toNat)
                    (fun _ ⟨sc0, ⟨⟩⟩ m2 ⟨hm2, hsc0⟩ => ?_)
                    (fun J3 hJ3 => by
                      c0_hsplit
                      · c0_hsteps; exact hJ3 (1#32, ()) mL ⟨rfl, by decide⟩
                      · have hraw_pos : 1 ≤ raw_sc.toNat :=
                          Nat.pos_of_ne_zero fun h0 => hc (BitVec.eq_of_toNat_eq h0)
                        c0_hsteps; exact hJ3 (raw_sc, ()) mL ⟨rfl, hraw_pos⟩)
                  subst m2
                  refine wp_join_group (ts := [i32])
                    (fun (sc, ()) m3 => m3 = mL ∧ 1 ≤ sc.toNat ∧ sc.toNat ≤ 0x40000000)
                    (fun _ ⟨sc, ⟨⟩⟩ m3 ⟨hm3, hsc1, hscM⟩ => ?_)
                    (fun J4 hJ4 => by
                      c0_hsplit
                      · c0_hsteps; exact hJ4 (0x40000000#32, ()) mL ⟨rfl, by decide, by decide⟩
                      · c0_hsteps; exact hJ4 (sc0, ()) mL ⟨rfl, hsc0, Nat.le_of_not_lt hc⟩)
                  subst m3
                  have hlx_tr : ((lit ^^^ 1#32).setWidth 64).toNat <
                      sK.scratch.tarjan_reach.length := by
                    rw [m7b_zext32, hsK.scratch_ok.tarjan_reach_len]; omega
                  c0_hsteps_nogrp
                  refine wp_join_group (ts := [i64, i32])
                    (fun (cc', fi', ()) m4 => ∃ sN : FullState,
                      PreservesCoreSlice FullState.core sK sN ∧ sN.LengthsOk c ∧
                      cc'.toNat ≤ 2 * c.max_vars ∧ fi'.toNat ≤ sz.toNat ∧
                      FullExtScratchPres s sN ∧ (FullMem c sN ⋆ R) m4)
                    (fun _ ⟨cc', fi', ⟨⟩⟩ m4
                        ⟨sN, hcoreN, hsN, hcc', hfi', hpresN, hm4⟩ => ?_)
                    (fun J5 hJ5 => by
                      c0_hsplit
                      · have hcc_lt : cand_cnt.toNat < 2 * c.max_vars := by
                          rw [show c.max_vars % 2 ^ 64 = c.max_vars from
                            Nat.mod_eq_of_lt (by omega)] at hc
                          omega
                        have hcc_ws1 : cand_cnt.toNat < sK.scratch.work_stk1.length := by
                          rw [hsK.scratch_ok.work_stk1_len]; omega
                        have hcc_ws2 : cand_cnt.toNat < sK.scratch.work_stk2.length := by
                          rw [hsK.scratch_ok.work_stk2_len]; omega
                        c0_hsteps
                        let sN : FullState := { sK with scratch := { sK.scratch with
                          work_stk1 := sK.scratch.work_stk1.set cand_cnt.toNat lit
                          work_stk2 := sK.scratch.work_stk2.set cand_cnt.toNat sc } }
                        have hsN : sN.LengthsOk c := { hsK with scratch_ok :=
                          { hsK.scratch_ok with
                            work_stk1_len := by
                              dsimp only [sN]; rw [List.length_set, hsK.scratch_ok.work_stk1_len]
                            work_stk2_len := by
                              dsimp only [sN]
                              rw [List.length_set, hsK.scratch_ok.work_stk2_len] } }
                        have hcc1 : (cand_cnt + 1#64).toNat = cand_cnt.toNat + 1 :=
                          m7b_bv64_add1_lt hcc_lt (by omega)
                        exact hJ5 (cand_cnt + 1#64, fidx, ()) _
                          ⟨sN, rfl, hsN, by rw [hcc1]; omega, hfidx_le,
                            ⟨hpresK.1, hpresK.2⟩, by assumption⟩
                      · refine wp_join_group (ts := [i32])
                          (fun (fi', ()) m4 => m4 = mL ∧ fi'.toNat ≤ sz.toNat)
                          (fun _ ⟨fi', ⟨⟩⟩ m4 ⟨hm4, hfi'⟩ => by
                            subst m4; c0_hsteps
                            exact hJ5 (cand_cnt, fi', ()) mL
                              ⟨sK, rfl, hsK, hcc_le, hfi', hpresK, hmL⟩)
                          (fun J6 hJ6 => by
                            c0_hsplit
                            · c0_hsteps; exact hJ6 (k, ()) mL ⟨rfl, by omega⟩
                            · c0_hsteps; exact hJ6 (fidx, ()) mL ⟨rfl, hfidx_le⟩))
                  have hsum_bd : (sum_sc + sc.setWidth 64).toNat ≤
                      (k.toNat + 1) * 0x40000000 := by
                    rw [BitVec.toNat_add, m7b_zext32]
                    have hlt : sum_sc.toNat + sc.toNat < 2 ^ 64 := by
                      have := Nat.mul_le_mul_right 0x40000000 hk_le; omega
                    rw [Nat.mod_eq_of_lt hlt, Nat.add_mul, Nat.one_mul]; omega
                  c0_hsteps
                  exact hJ1 (_, cc', _, _, fi', _, ()) m4
                    ⟨sN, hcoreN, hsN, hsum_bd, hcc', hfi', hpresN, hm4⟩
                · have hsum_s : sum_sc.toNat ≤ (k.toNat + 1) * 0x40000000 :=
                    Nat.le_trans hsum_le (Nat.mul_le_mul_right _ (Nat.le_succ _))
                  c0_hsteps; exact hJ1 (sum_sc, cand_cnt, fcnt, tot_brk, fidx, best, ()) mK
                    ⟨sK, rfl, hsK, hsum_s, hcc_le, hfidx_le, hpresK, hmK⟩
              · have hsum_s : sum_sc.toNat ≤ (k.toNat + 1) * 0x40000000 :=
                  Nat.le_trans hsum_le (Nat.mul_le_mul_right _ (Nat.le_succ _))
                c0_hsteps; exact hJ1 (sum_sc, cand_cnt, fcnt, tot_brk, fidx, best, ()) mK
                  ⟨sK, rfl, hsK, hsum_s, hcc_le, hfidx_le, hpresK, hmK⟩)
        · -- `k ≥ sz` exit `J0`
          clear hc
          c0_hsplit
          · c0_hsteps; exact hQ (0xffffffff#64, ()) sK mK hceqK hsK hpresK hmK
          clear hc
          c0_hsplit
          · c0_hsteps; exact hQ (0xffffffff#64, ()) sK mK hceqK hsK hpresK hmK
          clear hc
          refine wp_join_group (ts := [i64])
            (fun (tot_s, ()) m1 => m1 = mK ∧ 0 < tot_s.toNat)
            (fun _ ⟨tot_s, ⟨⟩⟩ m1 ⟨hm1, hts_pos⟩ => ?_)
            (fun J1 hJ1 => by
              c0_hsplit
              · c0_hsteps; exact hJ1 (1#64, ()) mK ⟨rfl, by decide⟩
              · have hsum_pos : 0 < sum_sc.toNat :=
                  Nat.pos_of_ne_zero fun h0 => hc (BitVec.eq_of_toNat_eq h0)
                c0_hsteps; exact hJ1 (sum_sc, ()) mK ⟨rfl, hsum_pos⟩)
          subst m1
          have hts_ne : tot_s ≠ 0#64 := m7b_bv64_ne_zero_of_pos hts_pos
          c0_hsteps_nogrp
          refine m7b_rng_call hRng rfl hmK hsK fun rng s1 m2 hcore1 hs1 hsc1 hm2 => ?_
          have hceq1 : s1.core = s.core := Eq.trans hcore1 hceqK
          have hpres1 : FullExtScratchPres s s1 :=
            ⟨Eq.trans (by rw [hsc1]) hpresK.1, Eq.trans (by rw [hsc1]) hpresK.2⟩
          c0_hsteps_nogrp
          refine wp_join_group (ts := [i64, i32, i64])
            (fun (acc, picked, _idx, ()) m3 => (FullMem c s1 ⋆ R) m3)
            (fun _ ⟨acc, picked, _idx, ⟨⟩⟩ m3 hm3 => ?_)
            (fun J2 hJ2 => by
              refine wp_loop_safety_slice_pure (fullSafetySlice c) s1 R
                (fun sL (_, j, ()) => sL = s1 ∧ j.toNat ≤ cand_cnt.toNat)
                (fun (_, j, ()) => cand_cnt.toNat - j.toNat)
                (fun J3 hJ3 => by
                  c0_hsteps
                  exact hJ3 s1 (0#64, 0#64, ()) m2 hm2 rfl hs1 ⟨rfl, Nat.zero_le _⟩)
                (fun J3 sL (acc, j, ()) mL _hcoreL hsL ⟨hsLeq, hj_le⟩ hmL hJ3 => by
                  dsimp only [fullSafetySlice] at hsL hmL
                  subst sL
                  c0_hsplit
                  · have hj_lt : j.toNat < cand_cnt.toNat := hc
                    have hj_ws2 : j.toNat < s1.scratch.work_stk2.length := by
                      rw [hs1.scratch_ok.work_stk2_len]; omega
                    have hj_ws1 : j.toNat < s1.scratch.work_stk1.length := by
                      rw [hs1.scratch_ok.work_stk1_len]; omega
                    c0_hsteps_nogrp
                    c0_hsplit
                    · c0_hsteps; exact hJ2 (_, _, _, ()) mL hmL
                    · have hj1 : (j + 1#64).toNat = j.toNat + 1 :=
                        m7b_bv64_add1_lt hj_lt (by omega)
                      c0_hsteps
                      exact hJ3 s1 (_, j + 1#64, ()) mL hmL (by dsimp only; rw [hj1]; omega)
                        rfl hs1 ⟨rfl, by rw [hj1]; omega⟩
                  · c0_hsteps; exact hJ2 (acc, 0xffffffff#32, j, ()) mL hmL))
          refine wp_join_group (ts := [i64, i32])
            (fun (_acc2, picked2, ()) m4 => (FullMem c s1 ⋆ R) m4)
            (fun _ ⟨_acc2, picked2, ⟨⟩⟩ m4 hm4 => ?_)
            (fun J3 hJ3 => by
              c0_hsplit
              · c0_hsplit
                · refine wp_join_group (ts := [i64, i32, i32])
                    (fun (acc3, picked3, _, ()) m4 => (FullMem c s1 ⋆ R) m4)
                    (fun _ ⟨acc3, picked3, _, ⟨⟩⟩ m4 hm4 => by
                      c0_hsteps; exact hJ3 (acc3, picked3, ()) m4 hm4)
                    (fun J4 hJ4 => by
                      refine wp_loop_safety_slice_pure (fullSafetySlice c) s1 R
                        (fun sL (_, k2, ()) => sL = s1 ∧ k2.toNat ≤ sz.toNat)
                        (fun (_, k2, ()) => sz.toNat - k2.toNat)
                        (fun J5 hJ5 => by
                          have hfidx_le' : fidx.toNat ≤ sz.toNat := hfidx_le
                          c0_hsteps
                          exact hJ5 s1 (acc, fidx, ()) m3 hm3 rfl hs1 ⟨rfl, hfidx_le'⟩)
                        (fun J5 sL (accL, k2, ()) mL _hcoreL hsL ⟨hsLeq, hk2_le⟩ hmL hJ5 => by
                          dsimp only [fullSafetySlice] at hsL hmL
                          subst sL
                          c0_hsplit
                          · have hk2_lt : k2.toNat < sz.toNat := by
                              simp only [he0_def, hsz_def] at hc; exact hc
                            clear hc
                            have hk2_1 : (k2 + 1#32).toNat = k2.toNat + 1 :=
                              m7b_bv32_add1_lt hk2_lt
                            have hl2_ar : (e0.setWidth 64 + 3#64 + k2.setWidth 64).toNat <
                                s1.core.arena.length := by
                              rw [BitVec.toNat_add, BitVec.toNat_add, m7b_zext32, m7b_zext32,
                                show (3#64 : BitVec 64).toNat = 3 from rfl,
                                Nat.mod_eq_of_lt (by omega : e0.toNat + 3 < 2 ^ 64),
                                Nat.mod_eq_of_lt (by omega : e0.toNat + 3 + k2.toNat < 2 ^ 64),
                                hceq1, harl]; omega
                            c0_hsteps_nogrp
                            let lit2 :=
                              s1.core.arena[(e0.setWidth 64 + 3#64 + k2.setWidth 64).toNat]'hl2_ar
                            have hlit2_def : s1.core.arena[(e0.toNat +
                                BitVec.toNat (3 : BitVec 64) + k2.toNat) % 2 ^ 64]'(by
                                  rw [show BitVec.toNat (3 : BitVec 64) = 3 from rfl,
                                    Nat.mod_eq_of_lt (by omega : e0.toNat + 3 +
                                      k2.toNat < 2 ^ 64),
                                    hceq1, harl]; omega) = lit2 := by
                              dsimp only [lit2]; congr 1
                              try rw [BitVec.toNat_add, BitVec.toNat_add, m7b_zext32, m7b_zext32,
                                show BitVec.toNat (3 : BitVec 64) = 3 from rfl,
                                show (3#64 : BitVec 64).toNat = 3 from rfl,
                                Nat.mod_eq_of_lt (by omega : e0.toNat + 3 < 2 ^ 64)]
                            refine wp_join_group (ts := [i64, i32])
                              (fun (accM, _pickedM, ()) mM => (FullMem c s1 ⋆ R) mM)
                              (fun _ ⟨accM, _pickedM, ⟨⟩⟩ mM hmM => by
                                c0_hsteps; exact hJ5 s1 (accM, k2 + 1#32, ()) mM hmM
                                  (by dsimp only; rw [hk2_1]; omega) rfl hs1
                                  ⟨rfl, by rw [hk2_1]; omega⟩)
                              (fun J6 hJ6 => by
                                c0_hsplit
                                · have hlit2_lt : lit2.toNat < 2 * s.core.cur_vars := by
                                    simp only [he0_def, hlit2_def] at hc
                                    rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64),
                                      Nat.mod_eq_of_lt (by omega : 2 * s.core.cur_vars < 2 ^ 64)]
                                      at hc
                                    exact hc
                                  clear hc
                                  have hlit2_v : (lit2.setWidth 64).toNat <
                                      s1.core.vals.length := by
                                    rw [m7b_zext32, hceq1, hvl]; omega
                                  c0_hsteps_nogrp
                                  c0_hsplit
                                  · clear hc
                                    refine m7Break_call hBrk rfl hs1 hmL fun ba2 mA hmA => ?_
                                    refine wp_join_group (ts := [i64])
                                      (fun (idx2, ()) mB => mB = mA ∧ idx2.toNat < 32)
                                      (fun _ ⟨idx2, ⟨⟩⟩ mB ⟨hmB, hidx2⟩ => ?_)
                                      (fun J7 hJ7 => by
                                        c0_hsplit
                                        · c0_hsteps
                                          have hba2_lt : (ba2.setWidth 64).toNat < 32 := by
                                            rw [m7b_zext32]; exact Nat.lt_trans hc (by decide)
                                          exact hJ7 (ba2.setWidth 64, ()) mA ⟨rfl, hba2_lt⟩
                                        · c0_hsteps; exact hJ7 (31#64, ()) mA ⟨rfl, by decide⟩)
                                    subst mB
                                    have hidx2_sb : idx2.toNat <
                                        s1.scratch.scratch_buf.length := by
                                      rw [hs1.scratch_ok.scratch_buf_len]; omega
                                    c0_hsteps_nogrp
                                    refine wp_join_group (ts := [i32])
                                      (fun (_, ()) mC => mC = mA)
                                      (fun _ ⟨_, ⟨⟩⟩ mC hmC => ?_)
                                      (fun J8 hJ8 => by
                                        c0_hsplit <;> (c0_hsteps; exact hJ8 (_, ()) mA rfl))
                                    subst mC
                                    refine wp_join_group (ts := [i32])
                                      (fun (_, ()) mD => mD = mA)
                                      (fun _ ⟨_, ⟨⟩⟩ mD hmD => ?_)
                                      (fun J9 hJ9 => by
                                        c0_hsplit <;> (c0_hsteps; exact hJ9 (_, ()) mA rfl))
                                    subst mD
                                    c0_hsplit
                                    · c0_hsteps; exact hJ4 (_, lit2, k2, ()) mA hmA
                                    · c0_hsteps; exact hJ6 (_, picked, ()) mA hmA
                                  · c0_hsteps; exact hJ6 (accL, picked, ()) mL hmL
                                · c0_hsteps; exact hJ6 (accL, picked, ()) mL hmL)
                          · c0_hsteps; exact hJ4 (accL, picked, k2, ()) mL hmL))
                · c0_hsteps; exact hJ3 (acc, picked, ()) m3 hm3
              · c0_hsteps; exact hJ3 (acc, picked, ()) m3 hm3)
          refine wp_join_group (ts := [i32])
            (fun (_, ()) m5 => m5 = m4)
            (fun _ ⟨_, ⟨⟩⟩ m5 hm5 => ?_)
            (fun J4 hJ4 => by c0_hsplit <;> (c0_hsteps; exact hJ4 (_, ()) m4 rfl))
          subst m5
          refine wp_join_group (ts := [i64])
            (fun (_, ()) m6 => m6 = m4)
            (fun _ ⟨_, ⟨⟩⟩ m6 hm6 => ?_)
            (fun J5 hJ5 => by c0_hsplit <;> (c0_hsteps; exact hJ5 (_, ()) m4 rfl))
          subst m6
          c0_hsteps
          exact hQ _ s1 m4 hceq1 hs1 hpres1 hm4)

end LeanQbe.T.Examples.Kissat.FullM7Walk
