module

public import LeanQbe.T.Examples.Kissat.FullIngestLemmas1
public import LeanQbe.T.Examples.Kissat.FullIngestLemmas2

/-!
# Kissat `D-Full` Stage-4 Arena / Watch-Stack / Backtrack Proofs (`FullIngestLemmas`)

Root aggregator module re-exporting all `4` parametric `(Γ : Env)` `Func.wp`
proofs (`full_arena_next_wp`, `full_alloc_cl_wp`, `full_wstack_defrag_wp`, `full_backtrack_wp`)
and shared Stage-4 invariants/specs (`FullIngestSpecs`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

open scoped FullArenaTactics FullIngestTactics
open FullIngestSpecs

/-! ## `full_arena_next` and `full_alloc_cl` -/

theorem full_arena_next_wp (Γ : Env) :
    ∀ a m Q X, fullArenaNextSpec a m Q X → Func.wp Γ full_arena_next_body a m Q X := by
  rintro ⟨h, cref, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  have hcl := hlen.core_ok; have har_len := hcl.arena_len_arr; have hale := hcl.arena_len_le
  have hcap : c.arena_cap < 2 * dimacsBound := c.harena; unfold dimacsBound at hcap
  have hcref32 : cref.toNat < 2 ^ 32 := cref.isLt
  have hidx0 : cref.toNat % 2 ^ 64 = cref.toNat := Nat.mod_eq_of_lt (by omega)
  have hidx2 : (cref.toNat + 2) % 2 ^ 64 = cref.toNat + 2 := Nat.mod_eq_of_lt (by omega)
  have htrunc_al : BitVec.setWidth 32 (BitVec.ofNat 64 s.core.arena_len) =
      BitVec.ofNat 32 s.core.arena_len :=
    BitVec.eq_of_toNat_eq (by simp [Nat.mod_eq_of_lt (by omega : s.core.arena_len < 2 ^ 32)])
  full_steps
  · have hgt : cref.toNat + 3 > s.core.arena_len := by c0_bound
    rw [htrunc_al]; simpa [fullArenaNextOff, hgt] using hQ
  · have hle3 : cref.toNat + 3 ≤ s.core.arena_len := by c0_bound
    have hcref2_lt : cref.toNat + 2 < s.core.arena.length := by omega
    have hsz32 := (s.core.arena[cref.toNat + 2]'hcref2_lt).isLt
    have hgtp :
        cref.toNat + 3 + (s.core.arena[cref.toNat + 2]'hcref2_lt).toNat > s.core.arena_len := by
      have hc' := hc; simp only [hidx2] at hc'
      rw [Nat.mod_eq_of_lt (by omega : s.core.arena_len < 2 ^ 64), Nat.mod_eq_of_lt
        (by omega : cref.toNat + 3 + (s.core.arena[cref.toNat + 2]'hcref2_lt).toNat < 2 ^ 64)]
        at hc'
      omega
    rw [htrunc_al]
    simpa [fullArenaNextOff, show ¬ (cref.toNat + 3 > s.core.arena_len) by omega,
      List.getElem?_eq_getElem hcref2_lt, hgtp] using hQ
  · have hle3 : cref.toNat + 3 ≤ s.core.arena_len := by c0_bound
    have hcref_lt : cref.toNat < s.core.arena.length := by omega
    have hcref2_lt : cref.toNat + 2 < s.core.arena.length := by omega
    have hsz32 := (s.core.arena[cref.toNat + 2]'hcref2_lt).isLt
    have hshrk : s.core.arena[cref.toNat]'hcref_lt &&& 0x00800000#32 ≠ 0#32 := by
      simpa [hidx0] using hc
    have hlep :
        cref.toNat + 3 + (s.core.arena[cref.toNat + 2]'hcref2_lt).toNat ≤ s.core.arena_len := by
      rename_i hgt_c; have hc' := hgt_c; simp only [hidx2] at hc'
      rw [Nat.mod_eq_of_lt (by omega : s.core.arena_len < 2 ^ 64), Nat.mod_eq_of_lt
        (by omega : cref.toNat + 3 + (s.core.arena[cref.toNat + 2]'hcref2_lt).toNat < 2 ^ 64)]
        at hc'
      omega
    let p0 := cref.toNat + 3 + (s.core.arena[cref.toNat + 2]'hcref2_lt).toNat
    have hp0_bv : (cref.setWidth 64 + 3 +
        (s.core.arena[(cref.setWidth 64 + 2).toNat]'(by c0_bound)).setWidth 64) =
        BitVec.ofNat 64 p0 := by
      have hsub : (cref.setWidth 64 + 2).toNat = cref.toNat + 2 := by c0_bound
      apply BitVec.eq_of_toNat_eq; simp only [hsub]; c0_bound
    have hnext_eq : fullArenaNextOff s.core.arena s.core.arena_len cref.toNat =
        fullArenaSkipShrk s.core.arena s.core.arena_len p0 (s.core.arena_len - p0) := by
      unfold fullArenaNextOff
      simp only [show ¬ (cref.toNat + 3 > s.core.arena_len) by omega, ↓reduceIte,
        List.getElem?_eq_getElem hcref_lt, List.getElem?_eq_getElem hcref2_lt, Option.getD_some,
        show ¬ (cref.toNat + 3 +
          (s.core.arena[cref.toNat + 2]'hcref2_lt).toNat > s.core.arena_len) by omega,
        hshrk, ne_eq, not_false_eq_true]; rfl
    refine wp_loop_inv
      (fun (p, ()) m1 => m1 = m ∧ p.toNat ≤ s.core.arena_len ∧
        fullArenaSkipShrk s.core.arena s.core.arena_len p.toNat (s.core.arena_len - p.toNat) =
          fullArenaSkipShrk s.core.arena s.core.arena_len p0 (s.core.arena_len - p0))
      (fun (p, ()) _ => s.core.arena_len - p.toNat)
      (fun J hLoop => ?_) (fun J (p, ()) m1 ⟨rfl, hple, hskip⟩ hLoop => ?_)
    · c0_steps; exact hLoop _ _ ⟨rfl, by rw [hp0_bv]; c0_bound, by
        rw [hp0_bv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : p0 < 2 ^ 64)]⟩
    · c0_steps
      · have hplt : p.toNat < s.core.arena_len := by c0_bound
        have hpar : p.toNat < s.core.arena.length := by omega
        have hne : s.core.arena[p.toNat]'hpar ≠ 0xFFFFFFFF#32 := hc
        have hstep : fullArenaSkipShrk s.core.arena s.core.arena_len (p.toNat + 1)
            (s.core.arena_len - (p.toNat + 1)) =
            fullArenaSkipShrk s.core.arena s.core.arena_len p.toNat
              (s.core.arena_len - p.toNat) := by
          conv => rhs; rw [show s.core.arena_len - p.toNat =
            (s.core.arena_len - (p.toNat + 1)) + 1 by omega]
                  unfold fullArenaSkipShrk
          simp only [hplt, ↓reduceIte, List.getElem?_eq_getElem hpar, Option.getD_some,
            hne, ne_eq, not_false_eq_true]
        refine hLoop _ _ (by c0_bound) ⟨rfl, by c0_bound, ?_⟩
        rw [show (p + 1).toNat = p.toNat + 1 by c0_bound, hstep, hskip]
      · have hplt : p.toNat < s.core.arena_len := by c0_bound
        have hpar : p.toNat < s.core.arena.length := by omega
        have heq_ff : s.core.arena[p.toNat]'hpar = 0xFFFFFFFF#32 := by assumption
        rw [hnext_eq, ← hskip,
          show s.core.arena_len - p.toNat = (s.core.arena_len - (p.toNat + 1)) + 1 by omega] at hQ
        simp only [fullArenaSkipShrk, hplt, ↓reduceIte, List.getElem?_eq_getElem hpar,
          Option.getD_some, heq_ff] at hQ
        rw [show (p + 1).setWidth 32 = BitVec.ofNat 32 (p.toNat + 1) from
          BitVec.eq_of_toNat_eq (by c0_bound)]; exact hQ
      · have hpeq : p.toNat = s.core.arena_len := by c0_bound
        rw [hnext_eq, ← hskip, hpeq, Nat.sub_self] at hQ
        simp only [fullArenaSkipShrk, Nat.min_self] at hQ
        rw [show p.setWidth 32 = BitVec.ofNat 32 s.core.arena_len from
          BitVec.eq_of_toNat_eq (by c0_bound)]; exact hQ
  · have hle3 : cref.toNat + 3 ≤ s.core.arena_len := by c0_bound
    have hcref_lt : cref.toNat < s.core.arena.length := by omega
    have hcref2_lt : cref.toNat + 2 < s.core.arena.length := by omega
    have hsz32 := (s.core.arena[cref.toNat + 2]'hcref2_lt).isLt
    have hshrk : s.core.arena[cref.toNat]'hcref_lt &&& 0x00800000#32 = 0#32 := by
      simpa [hidx0] using hc
    have hlep :
        cref.toNat + 3 + (s.core.arena[cref.toNat + 2]'hcref2_lt).toNat ≤ s.core.arena_len := by
      rename_i hgt_c; have hc' := hgt_c; simp only [hidx2] at hc'
      rw [Nat.mod_eq_of_lt (by omega : s.core.arena_len < 2 ^ 64), Nat.mod_eq_of_lt
        (by omega : cref.toNat + 3 + (s.core.arena[cref.toNat + 2]'hcref2_lt).toNat < 2 ^ 64)]
        at hc'
      omega
    have hfin : fullArenaNextOff s.core.arena s.core.arena_len cref.toNat =
        cref.toNat + 3 + (s.core.arena[cref.toNat + 2]'hcref2_lt).toNat := by
      unfold fullArenaNextOff
      simp only [show ¬ (cref.toNat + 3 > s.core.arena_len) by omega, ↓reduceIte,
        List.getElem?_eq_getElem hcref_lt, List.getElem?_eq_getElem hcref2_lt, Option.getD_some,
        show ¬ (cref.toNat + 3 +
          (s.core.arena[cref.toNat + 2]'hcref2_lt).toNat > s.core.arena_len) by omega,
        hshrk, ne_eq, not_true_eq_false]
    rw [hfin] at hQ
    have hsub : (cref.setWidth 64 + 2).toNat = cref.toNat + 2 := by c0_bound
    rw [show (cref.setWidth 64 + 3 +
        (s.core.arena[(cref.setWidth 64 + 2).toNat]'(by c0_bound)).setWidth 64).setWidth 32 =
        BitVec.ofNat 32 (cref.toNat + 3 + (s.core.arena[cref.toNat + 2]'hcref2_lt).toNat) from
      BitVec.eq_of_toNat_eq (by simp only [hsub]; c0_bound)]
    exact hQ

private theorem bv32_and_two_pow_eq_zero {g : BitVec 32} {k : Nat}
    (hg : g.toNat < 2 ^ 19) (hk : 19 ≤ k) (hk32 : k < 32) :
    g &&& BitVec.ofNat 32 (2 ^ k) = 0#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero]
  by_cases hik : i = k
  · subst hik; rw [BitVec.getLsbD_eq_getElem hi, BitVec.getElem_eq_testBit_toNat,
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hg (Nat.pow_le_pow_right (by omega) hk))]; simp
  · rw [BitVec.getLsbD_eq_getElem hi (x := BitVec.ofNat 32 (2 ^ k)),
      BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) hk32), Nat.testBit_two_pow]
    simp [Ne.symm hik]

private theorem alloc_hdr_bits (g : BitVec 32) (red : Bool) (hg : g.toNat ≤ 0x7FFFF) :
    let w := g ||| (if red then 0x00400000#32 else 0#32)
    (w &&& 0x00800000#32) = 0#32 ∧ (w &&& 0x00080000#32) = 0#32 ∧
    ((w &&& 0x00400000#32) ≠ 0#32 ↔ red = true) := by
  intro w; have hg' : g.toNat < 2 ^ 19 := Nat.lt_of_le_of_lt hg (by decide)
  have h1 := bv32_and_two_pow_eq_zero (k := 23) hg' (by omega) (by omega)
  have h2 := bv32_and_two_pow_eq_zero (k := 19) hg' (by omega) (by omega)
  have h3 := bv32_and_two_pow_eq_zero (k := 22) hg' (by omega) (by omega)
  cases red
  · simp [w, h1, h2, h3]
  · refine ⟨?_, ?_, ?_⟩
    · apply BitVec.eq_of_getElem_eq; intro i hi
      have := congrArg (fun x => x[i]'hi) h1
      have := congrArg (fun x => x[i]'hi) (by decide : (0x00400000#32 &&& 0x00800000#32) = 0#32)
      simp only [w, ↓reduceIte, BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_zero] at *
      grind
    · apply BitVec.eq_of_getElem_eq; intro i hi
      have := congrArg (fun x => x[i]'hi) h2
      have := congrArg (fun x => x[i]'hi) (by decide : (0x00400000#32 &&& 0x00080000#32) = 0#32)
      simp only [w, ↓reduceIte, BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_zero] at *
      grind
    · simp only [w, ↓reduceIte, iff_true]; intro h0
      have hb := congrArg (fun x => x.getLsbD 22) h0; simp at hb

theorem full_alloc_cl_wp (Γ : Env) :
    ∀ a m Q X, fullAllocClSpec a m Q X → Func.wp Γ full_alloc_cl_body a m Q X := by
  rintro ⟨h, sz, glue, red, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  have hcl := hlen.core_ok; have hsl := hlen.scratch_ok
  have har_len := hcl.arena_len_arr; have hale := hcl.arena_len_le
  have hcap : c.arena_cap < 2 * dimacsBound := c.harena; unfold dimacsBound at hcap
  full_steps
  · have hlt : c.arena_cap - s.core.arena_len < 3 + sz.toNat := by c0_bound
    simp only [hlt, ↓reduceIte] at hQ; exact hQ
  all_goals
    have hsz32 : sz.toNat < 2 ^ 32 := sz.isLt
    have hge : ¬ (c.arena_cap - s.core.arena_len < 3 + sz.toNat) := by c0_bound
    simp only [hge, ↓reduceIte] at hQ
    have hfit : s.core.arena_len + 3 + sz.toNat ≤ c.arena_cap := by omega
    have hne_al : (BitVec.ofNat 64 s.core.arena_len + (3 + sz.setWidth 64)).toNat =
        s.core.arena_len + 3 + sz.toNat := by c0_bound
    have h1_eq : (BitVec.ofNat 64 s.core.arena_len + 1).toNat = s.core.arena_len + 1 := by c0_bound
    have h2_eq : (BitVec.ofNat 64 s.core.arena_len + 2).toNat = s.core.arena_len + 2 := by c0_bound
    have h0_eq : (BitVec.ofNat 64 s.core.arena_len).toNat = s.core.arena_len := by c0_bound
    rw [hne_al, h0_eq, h1_eq, h2_eq] at hm
    refine hQ _ _ ⟨{ hcl with arena_len_arr := by simp [har_len], arena_len_le := hfit }, hsl⟩
      (fun k hk => by rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega)]) ?_ ?_ ?_ ?_ hm
    · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_self (by omega), Option.getD_some]
      first | exact (alloc_hdr_bits 0x7FFFF#32 true (by decide)).1
            | exact (alloc_hdr_bits 0x7FFFF#32 false (by decide)).1
            | exact (alloc_hdr_bits glue true (by c0_bound)).1
            | exact (alloc_hdr_bits glue false (by c0_bound)).1
    · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_self (by omega), Option.getD_some]
      first | exact (alloc_hdr_bits 0x7FFFF#32 true (by decide)).2.1
            | exact (alloc_hdr_bits 0x7FFFF#32 false (by decide)).2.1
            | exact (alloc_hdr_bits glue true (by c0_bound)).2.1
            | exact (alloc_hdr_bits glue false (by c0_bound)).2.1
    · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_self (by omega), Option.getD_some]
      first | (subst hc; exact (alloc_hdr_bits 0x7FFFF#32 true (by decide)).2.2)
            | (subst hc; exact (alloc_hdr_bits 0x7FFFF#32 false (by decide)).2.2)
            | (subst hc; exact (alloc_hdr_bits glue true (by c0_bound)).2.2)
            | (subst hc; exact (alloc_hdr_bits glue false (by c0_bound)).2.2)
    · rw [List.getElem?_set_self (by simp [har_len]; omega), Option.getD_some]

end LeanQbe.T.Examples.Kissat.Full