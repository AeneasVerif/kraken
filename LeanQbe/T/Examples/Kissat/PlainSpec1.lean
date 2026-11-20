module

public import LeanQbe.T.Examples.Kissat.PlainArena
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Plain` Arena/Watch Invariants & Soundness Lemmas (`Stage 3`)

Builds on `PlainArena` to define:
1. `COMPACT` `ward` 32-bit word-arena clause projections (`arenaHdr`, `arenaClauseSize`,
   `arenaClauseGarb`, `arenaClauseLits`, `arenaNextOff`, `arenaClauseRefs`, `ArenaClausesInv`).
2. Contiguous watch `vectors` (`watchOff`, `watchSize`, `WatchSliceOk`, `WatchesInv`) supporting
   both tagged binary watches (`PW_BIN_FLAG`) and blocking-literal large watches.
3. Three-way reason trail & minimization invariants (`PlainCoreInv` / `PlainTrailInv`,
   `MarksClear`, `PlainMinMarkInv`, `PlainInv`), preserving separation between soundness fields
   and `PlainHeur`.
4. Preservation & soundness proofs (`assign_preserves_core`, `addClause_preserves_core`,
   `swapCl_preserves_core`, `plainInv_init`, `plainMinMark_entails`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Plain

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

/-! ## 1. `COMPACT` `ward` arena clause projections and block scanning -/

def arenaHdr (s : PlainState) (cref : Nat) : BitVec 32 :=
  s.arena[cref]?.getD 0#32

def arenaClauseSize (s : PlainState) (cref : Nat) : Nat :=
  (s.arena[cref + 2]?.getD 0#32).toNat

def arenaClauseGarb (s : PlainState) (cref : Nat) : Bool :=
  (arenaHdr s cref &&& 0x00080000#32) != 0#32

def arenaClauseLits (s : PlainState) (cref : Nat) : List Nat :=
  ((s.arena.drop (cref + 3)).take (arenaClauseSize s cref)).map BitVec.toNat

theorem mem_arenaClauseLits_iff {s : PlainState} {cref l : Nat}
    (h : cref + 3 + arenaClauseSize s cref ≤ s.arena.length) :
    l ∈ arenaClauseLits s cref ↔
      ∃ (k : Nat) (_hk : k < arenaClauseSize s cref),
        (s.arena[cref + 3 + k]'(by omega)).toNat = l := by
  unfold arenaClauseLits
  rw [List.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hx
    have hk' : k < arenaClauseSize s cref := by
      rw [List.length_take, List.length_drop] at hk; omega
    refine ⟨k, hk', ?_⟩
    rw [List.getElem_take, List.getElem_drop] at hget
    exact congrArg BitVec.toNat hget
  · rintro ⟨k, hk, hget⟩
    refine ⟨s.arena[cref + 3 + k]'(by omega), ?_, hget⟩
    have hlt : k < ((s.arena.drop (cref + 3)).take (arenaClauseSize s cref)).length := by
      rw [List.length_take, List.length_drop]; omega
    have hmem := List.getElem_mem hlt
    simpa [List.getElem_take, List.getElem_drop] using hmem

def arenaSkipShrk (ar : List (BitVec 32)) (alen p : Nat) : Nat → Nat
  | 0 => min p alen
  | fuel + 1 =>
    if p < alen then
      if ar[p]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 then
        arenaSkipShrk ar alen (p + 1) fuel
      else p + 1
    else alen

theorem arenaSkipShrk_bounds {ar : List (BitVec 32)} {alen : Nat} :
    ∀ {fuel p : Nat}, p ≤ alen → p ≤ arenaSkipShrk ar alen p fuel ∧
      arenaSkipShrk ar alen p fuel ≤ alen
  | 0, p, hle => by simp [arenaSkipShrk]; omega
  | fuel + 1, p, hle => by
    unfold arenaSkipShrk
    split
    · split
      · have ih := arenaSkipShrk_bounds (ar := ar) (alen := alen) (fuel := fuel) (p := p + 1)
          (by omega)
        omega
      · omega
    · omega

/-- Word offset of the block immediately following `cref` (matches `plain_arena_next`). -/
def arenaNextOff (ar : List (BitVec 32)) (alen cref : Nat) : Nat :=
  if cref + 3 > alen then alen
  else
    let hdr := ar[cref]?.getD 0#32
    let sz := (ar[cref + 2]?.getD 0#32).toNat
    let p := cref + 3 + sz
    if p > alen then alen
    else if (hdr &&& 0x00800000#32) ≠ 0#32 then
      arenaSkipShrk ar alen p (alen - p)
    else p

theorem arenaNextOff_bounds {ar : List (BitVec 32)} {alen cref : Nat}
    (hle : cref + 3 ≤ alen) :
    cref < arenaNextOff ar alen cref ∧ arenaNextOff ar alen cref ≤ alen := by
  unfold arenaNextOff
  have hnot : ¬ (cref + 3 > alen) := by omega
  simp only [hnot, ↓reduceIte]
  split
  · exact ⟨by omega, by omega⟩
  · split
    · rename_i hle_p _
      have hb := arenaSkipShrk_bounds (ar := ar) (alen := alen)
        (p := cref + 3 + (ar[cref + 2]?.getD 0#32).toNat)
        (fuel := alen - (cref + 3 + (ar[cref + 2]?.getD 0#32).toNat)) (by omega)
      omega
    · exact ⟨by omega, by omega⟩

def arenaScanRefs (ar : List (BitVec 32)) (alen pos : Nat) : Nat → List Nat
  | 0 => []
  | fuel + 1 =>
    if pos + 3 ≤ alen then
      let nxt := arenaNextOff ar alen pos
      pos :: arenaScanRefs ar alen nxt fuel
    else []

def arenaClauseRefs (s : PlainState) : List Nat :=
  arenaScanRefs s.arena s.arena_len 0 s.arena_len

theorem arenaScanRefs_fuel_ge {ar : List (BitVec 32)} {alen : Nat} :
    ∀ {f1 f2 pos : Nat}, alen - pos ≤ f1 → alen - pos ≤ f2 →
      arenaScanRefs ar alen pos f1 = arenaScanRefs ar alen pos f2
  | 0, f2, pos, h1, _ => by
    have hp : ¬ (pos + 3 ≤ alen) := by omega
    cases f2 <;> simp [arenaScanRefs, hp]
  | f1 + 1, 0, pos, _, h2 => by
    have hp : ¬ (pos + 3 ≤ alen) := by omega
    simp [arenaScanRefs, hp]
  | f1 + 1, f2 + 1, pos, h1, h2 => by
    unfold arenaScanRefs
    split
    · rename_i hle
      have hnb := arenaNextOff_bounds (ar := ar) (alen := alen) (cref := pos) hle
      dsimp only
      rw [arenaScanRefs_fuel_ge (ar := ar) (alen := alen) (f1 := f1) (f2 := f2)
        (pos := arenaNextOff ar alen pos) (by omega) (by omega)]
    · rfl

theorem arenaScanRefs_mem_bounds {ar : List (BitVec 32)} {alen : Nat} :
    ∀ {fuel pos r : Nat}, r ∈ arenaScanRefs ar alen pos fuel →
      pos ≤ r ∧ r + 3 ≤ alen
  | 0, _, _, h => by simp [arenaScanRefs] at h
  | fuel + 1, pos, r, h => by
    unfold arenaScanRefs at h
    split at h
    · rename_i hle
      simp only [List.mem_cons] at h
      rcases h with rfl | hrest
      · exact ⟨Nat.le_refl _, hle⟩
      · have hb := arenaNextOff_bounds (ar := ar) (alen := alen) (cref := pos) hle
        have ih := arenaScanRefs_mem_bounds hrest
        omega
    · simp at h

theorem arenaScanRefs_disjoint {ar : List (BitVec 32)} {alen : Nat} :
    ∀ {fuel pos r1 r2 : Nat},
      r1 ∈ arenaScanRefs ar alen pos fuel →
      r2 ∈ arenaScanRefs ar alen pos fuel →
      r1 < r2 → arenaNextOff ar alen r1 ≤ r2
  | 0, _, _, _, h1, _, _ => by simp [arenaScanRefs] at h1
  | fuel + 1, pos, r1, r2, h1, h2, hlt => by
    unfold arenaScanRefs at h1 h2
    split at h1
    · rename_i hle
      simp only [hle, ↓reduceIte, List.mem_cons] at h1 h2
      have hb := arenaNextOff_bounds (ar := ar) (alen := alen) (cref := pos) hle
      rcases h1 with rfl | h1' <;> rcases h2 with rfl | h2'
      · omega
      · exact (arenaScanRefs_mem_bounds h2').1
      · have hb1 := arenaScanRefs_mem_bounds h1'; omega
      · exact arenaScanRefs_disjoint h1' h2' hlt
    · simp at h1

theorem arenaScanRefs_congr {ar1 ar2 : List (BitVec 32)} {alen : Nat} :
    ∀ {fuel pos : Nat},
      (∀ r ∈ arenaScanRefs ar1 alen pos fuel,
        arenaNextOff ar2 alen r = arenaNextOff ar1 alen r) →
      arenaScanRefs ar2 alen pos fuel = arenaScanRefs ar1 alen pos fuel
  | 0, _, _ => rfl
  | fuel + 1, pos, h => by
    unfold arenaScanRefs
    split
    · rename_i hle
      have heq : arenaNextOff ar2 alen pos = arenaNextOff ar1 alen pos :=
        h pos (by simp [arenaScanRefs, hle])
      dsimp only; rw [heq]
      rw [arenaScanRefs_congr (ar1 := ar1) (ar2 := ar2) (alen := alen) (fuel := fuel)
        (pos := arenaNextOff ar1 alen pos) fun r hr => h r (by simp [arenaScanRefs, hle, hr])]
    · rfl

theorem arenaClauseRefs_congr {s1 s2 : PlainState} (hlen : s2.arena_len = s1.arena_len)
    (heq : ∀ r ∈ arenaClauseRefs s1,
      arenaNextOff s2.arena s1.arena_len r = arenaNextOff s1.arena s1.arena_len r) :
    arenaClauseRefs s2 = arenaClauseRefs s1 := by
  unfold arenaClauseRefs; rw [hlen]; exact arenaScanRefs_congr heq

theorem arenaSkipShrk_congr {ar1 ar2 : List (BitVec 32)} {alen : Nat} :
    ∀ {fuel p : Nat},
      (∀ k, p ≤ k → k < arenaSkipShrk ar1 alen p fuel → ar2[k]? = ar1[k]?) →
      arenaSkipShrk ar2 alen p fuel = arenaSkipShrk ar1 alen p fuel
  | 0, _, _ => rfl
  | fuel + 1, p, heq => by
    unfold arenaSkipShrk; split
    · rename_i hlt
      have hb := arenaSkipShrk_bounds (ar := ar1) (alen := alen) (fuel := fuel) (p := p + 1)
        (by omega)
      have h0 : p < arenaSkipShrk ar1 alen p (fuel + 1) := by
        unfold arenaSkipShrk; simp only [hlt, ↓reduceIte]; split <;> omega
      have hpk : ar2[p]? = ar1[p]? := heq p (Nat.le_refl p) h0
      simp only [hpk]; split
      · rename_i hne
        refine arenaSkipShrk_congr (fuel := fuel) (p := p + 1) fun k hk1 hk2 =>
          heq k (by omega) (by unfold arenaSkipShrk; simp only [hlt, hne, ↓reduceIte, ne_eq,
            not_false_eq_true]; exact hk2)
      · rfl
    · rfl

theorem arenaNextOff_congr_block {ar1 ar2 : List (BitVec 32)} {alen r : Nat}
    (h0 : ar2[r]? = ar1[r]?) (h2 : ar2[r + 2]? = ar1[r + 2]?)
    (hpad : ∀ k, r + 3 + (ar1[r + 2]?.getD 0#32).toNat ≤ k →
      k < arenaNextOff ar1 alen r → ar2[k]? = ar1[k]?) :
    arenaNextOff ar2 alen r = arenaNextOff ar1 alen r := by
  unfold arenaNextOff; split
  · rfl
  · rename_i hnot; simp only [h0, h2]; split
    · rfl
    · split
      · rename_i hle_p hshrk
        refine arenaSkipShrk_congr fun k hk1 hk2 => hpad k hk1 ?_
        unfold arenaNextOff; simp only [hnot, ↓reduceIte, hle_p, hshrk, ne_eq,
          not_false_eq_true]; exact hk2
      · rfl

theorem arenaScanRefs_last {ar : List (BitVec 32)} {alen : Nat} :
    ∀ {fuel pos : Nat}, alen - pos ≤ fuel → pos + 3 ≤ alen →
      (∀ r ∈ arenaScanRefs ar alen pos fuel,
        arenaNextOff ar alen r = alen ∨ arenaNextOff ar alen r + 3 ≤ alen) →
      ∃ r ∈ arenaScanRefs ar alen pos fuel, arenaNextOff ar alen r = alen
  | 0, _, hfl, hle, _ => by omega
  | fuel + 1, pos, hfl, hle, hchain => by
    unfold arenaScanRefs at hchain ⊢; simp only [hle, ↓reduceIte] at hchain ⊢
    rcases hchain pos List.mem_cons_self with hlast | hmore
    · exact ⟨pos, List.mem_cons_self, hlast⟩
    · have hb := arenaNextOff_bounds (ar := ar) (alen := alen) (cref := pos) hle
      obtain ⟨r, hr, hre⟩ := arenaScanRefs_last (fuel := fuel) (pos := arenaNextOff ar alen pos)
        (by omega) hmore fun r' hr' => hchain r' (List.mem_cons_of_mem _ hr')
      exact ⟨r, List.mem_cons_of_mem _ hr, hre⟩

private theorem arenaScanRefs_append_one {ar : List (BitVec 32)} {alen sz : Nat}
    (hsz : 3 ≤ sz) (hhdr : (ar[alen]?.getD 0#32 &&& 0x00800000#32) = 0#32)
    (hsz_eq : (ar[alen + 2]?.getD 0#32).toNat = sz) :
    ∀ fuel, 2 ≤ fuel → arenaScanRefs ar (alen + 3 + sz) alen fuel = [alen]
  | fuel + 1, hf => by
    have hp : alen + 3 ≤ alen + 3 + sz := by omega
    have hnxt : arenaNextOff ar (alen + 3 + sz) alen = alen + 3 + sz := by
      unfold arenaNextOff; simp [hsz_eq, hhdr]
    cases fuel with
    | zero => omega
    | succ f' =>
      have hp2 : ¬ (alen + 3 + sz + 3 ≤ alen + 3 + sz) := by omega
      simp [arenaScanRefs, hp, hnxt, hp2]

theorem arenaScanRefs_eq_of_prefix {ar1 ar2 : List (BitVec 32)} {alen sz : Nat}
    (hsz : 3 ≤ sz) (hhdr2 : (ar2[alen]?.getD 0#32 &&& 0x00800000#32) = 0#32)
    (hsz2 : (ar2[alen + 2]?.getD 0#32).toNat = sz)
    (hchain : ∀ pos, pos ∈ arenaScanRefs ar1 alen 0 alen →
      arenaNextOff ar1 alen pos = alen ∨
      arenaNextOff ar1 alen pos + 3 ≤ alen)
    (hlast : alen = 0 ∨ ∃ r ∈ arenaScanRefs ar1 alen 0 alen, arenaNextOff ar1 alen r = alen)
    (hhold : ∀ r ∈ arenaScanRefs ar1 alen 0 alen,
      arenaNextOff ar2 (alen + 3 + sz) r = arenaNextOff ar1 alen r) :
    arenaScanRefs ar2 (alen + 3 + sz) 0 (alen + 3 + sz) =
      arenaScanRefs ar1 alen 0 alen ++ [alen] := by
  have go : ∀ (fuel pos : Nat),
      alen - pos ≤ fuel →
      (pos = alen ∨ (pos + 3 ≤ alen ∧
        (∀ r ∈ arenaScanRefs ar1 alen pos fuel,
          arenaNextOff ar1 alen r = alen ∨ arenaNextOff ar1 alen r + 3 ≤ alen))) →
      (∀ r ∈ arenaScanRefs ar1 alen pos fuel,
        arenaNextOff ar2 (alen + 3 + sz) r = arenaNextOff ar1 alen r) →
      arenaScanRefs ar2 (alen + 3 + sz) pos (fuel + 3 + sz) =
        arenaScanRefs ar1 alen pos fuel ++ [alen] := by
    intro fuel
    induction fuel with
    | zero =>
      intro pos hfl hpos _
      rcases hpos with rfl | ⟨hle, _⟩
      · simp [arenaScanRefs]
        exact arenaScanRefs_append_one hsz hhdr2 hsz2 (3 + sz) (by omega)
      · omega
    | succ f ih =>
      intro pos hfl hpos hsub
      rcases hpos with rfl | ⟨hle, hstep_ok⟩
      · have h1 : ¬ (pos + 3 ≤ pos) := by omega
        rw [arenaScanRefs]; simp only [h1, ↓reduceIte, List.nil_append]
        exact arenaScanRefs_append_one hsz hhdr2 hsz2 (f + 1 + 3 + sz) (by omega)
      · have hp2 : pos + 3 ≤ alen + 3 + sz := by omega
        have hnxt : arenaNextOff ar2 (alen + 3 + sz) pos = arenaNextOff ar1 alen pos :=
          hsub pos (by simp [arenaScanRefs, hle])
        have hb := arenaNextOff_bounds (ar := ar1) (alen := alen) (cref := pos) hle
        have hstep : f + 1 + 3 + sz = (f + 3 + sz) + 1 := by omega
        rw [hstep]; unfold arenaScanRefs
        simp only [hle, hp2, ↓reduceIte, hnxt, List.cons_append]
        congr 1
        have hok := hstep_ok pos (by simp [arenaScanRefs, hle])
        refine ih (arenaNextOff ar1 alen pos) (by omega) ?_ ?_
        · rcases hok with hn | hn3
          · exact Or.inl hn
          · exact Or.inr ⟨hn3, fun r hr => hstep_ok r (by simp [arenaScanRefs, hle, hr])⟩
        · intro r hr; exact hsub r (by simp [arenaScanRefs, hle, hr])
  rcases hlast with rfl | ⟨r, hr, _⟩
  · exact go 0 0 (by omega) (Or.inl rfl) (fun _ h => by simp [arenaScanRefs] at h)
  · have ha3 : 3 ≤ alen := by
      have := arenaScanRefs_mem_bounds hr; omega
    have hgo := go alen 0 (by omega) (Or.inr ⟨ha3, hchain⟩) hhold
    simpa [Nat.add_assoc] using hgo

/-- Arena clause-database invariant (`ArenaClausesInv`): contiguous word-arena blocks in
`0 ..< s.arena_len`, every live (non-garbage) clause has size `≥ 3`, literals `< 2 * mv`, and
is semantically entailed by `F0`. -/
structure ArenaClausesInv (c : PlainCfg) (F0 : CNF Nat) (s : PlainState) : Prop where
  len_ok : s.arena_len = 0 ∨ 3 ≤ s.arena_len
  refs_wf : ∀ r ∈ arenaClauseRefs s,
    r + 3 ≤ s.arena_len ∧ 3 ≤ arenaClauseSize s r ∧
    r + 3 + arenaClauseSize s r ≤ arenaNextOff s.arena s.arena_len r ∧
    arenaNextOff s.arena s.arena_len r ≤ s.arena_len ∧
    (arenaNextOff s.arena s.arena_len r = s.arena_len ∨
     arenaNextOff s.arena s.arena_len r + 3 ≤ s.arena_len)
  lits_lt : ∀ r ∈ arenaClauseRefs s, arenaClauseGarb s r = false →
    ∀ l ∈ arenaClauseLits s r, l < 2 * c.mv
  entails : ∀ r ∈ arenaClauseRefs s, arenaClauseGarb s r = false →
    F0.EntailsClause (cnfClause (arenaClauseLits s r))

theorem ArenaClausesInv.mono {c : PlainCfg} {F0 F1 : CNF Nat} {s : PlainState}
    (hF : F1.Entails F0) (h : ArenaClausesInv c F0 s) : ArenaClausesInv c F1 s :=
  { h with entails := fun r hr hg => CNF.entails_clause_trans hF (h.entails r hr hg) }

theorem ArenaClausesInv.disjoint {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (h : ArenaClausesInv c F0 s) {r1 r2 : Nat}
    (hr1 : r1 ∈ arenaClauseRefs s) (hr2 : r2 ∈ arenaClauseRefs s) (hlt : r1 < r2) :
    r1 + 3 + arenaClauseSize s r1 ≤ r2 := by
  have h1 := arenaScanRefs_disjoint hr1 hr2 hlt
  have h2 := (h.refs_wf r1 hr1).2.2.1
  omega

theorem ArenaClausesInv.chain_end {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (h : ArenaClausesInv c F0 s) : s.arena_len = 0 ∨
      ∃ r ∈ arenaClauseRefs s, arenaNextOff s.arena s.arena_len r = s.arena_len := by
  rcases h.len_ok with hz | h3
  · exact Or.inl hz
  · exact Or.inr (arenaScanRefs_last (by omega) h3 fun r hr => (h.refs_wf r hr).2.2.2.2)

/-! ## 2. Watch `vectors` and contiguous watch stack (`WatchesInv`) -/

def watchOff (s : PlainState) (l : Nat) : Nat :=
  (s.wvec[2 * l]?.getD 0#32).toNat

def watchSize (s : PlainState) (l : Nat) : Nat :=
  (s.wvec[2 * l + 1]?.getD 0#32).toNat

/-- Well-formedness of one literal's slice `s.wstk[p ..< p + rem]` in `D-Plain`:
- binary watches (`w0 &&& 0x80000000 ≠ 0`): 1 word encoding `other < 2 * c.mv` with
  `F0 ⊨ [lit, other]`;
- large watches (`w0 &&& 0x80000000 = 0`): 2 words `(w0, cref)` with `cref ∈ arenaClauseRefs s`. -/
inductive WatchSliceOk (c : PlainCfg) (F0 : CNF Nat) (s : PlainState) (lit : Nat) :
    Nat → Nat → Prop where
  | empty {p} : WatchSliceOk c F0 s lit p 0
  | bin {p rem w0} :
      s.wstk[p]? = some w0 →
      (w0 &&& 0x80000000#32) ≠ 0#32 →
      (w0 &&& 0x7FFFFFFF#32).toNat < 2 * c.mv →
      F0.EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat]) →
      WatchSliceOk c F0 s lit (p + 1) rem →
      WatchSliceOk c F0 s lit p (rem + 1)
  | large {p rem w0 cref} :
      s.wstk[p]? = some w0 →
      s.wstk[p + 1]? = some cref →
      (w0 &&& 0x80000000#32) = 0#32 →
      cref.toNat < 0x80000000 →
      cref.toNat ∈ arenaClauseRefs s →
      WatchSliceOk c F0 s lit (p + 2) rem →
      WatchSliceOk c F0 s lit p (rem + 2)

theorem WatchSliceOk.mono {c : PlainCfg} {F0 F1 : CNF Nat} {s s' : PlainState} {lit p rem : Nat}
    (hF : F1.Entails F0)
    (hsub : ∀ r ∈ arenaClauseRefs s, r ∈ arenaClauseRefs s')
    (hwstk : ∀ k, p ≤ k → k < p + rem → s'.wstk[k]? = s.wstk[k]?)
    (h : WatchSliceOk c F0 s lit p rem) : WatchSliceOk c F1 s' lit p rem := by
  induction h with
  | empty => exact .empty
  | @bin p rem w0 hp hflag hlt hent hrest ih =>
    refine .bin (by rw [hwstk p (by omega) (by omega), hp]) hflag hlt
      (CNF.entails_clause_trans hF hent)
      (ih fun k hk1 hk2 => hwstk k (by omega) (by omega))
  | @large p rem w0 cref hp hp1 hflag hlt href hrest ih =>
    refine .large (by rw [hwstk p (by omega) (by omega), hp])
      (by rw [hwstk (p + 1) (by omega) (by omega), hp1])
      hflag hlt (hsub _ href) (ih fun k hk1 hk2 => hwstk k (by omega) (by omega))

structure WatchesInv (c : PlainCfg) (F0 : CNF Nat) (s : PlainState) : Prop where
  bounds : ∀ l < 2 * c.mv, watchOff s l + watchSize s l ≤ s.wlen
  slices : ∀ l < 2 * c.mv, WatchSliceOk c F0 s l (watchOff s l) (watchSize s l)

theorem WatchesInv.mono {c : PlainCfg} {F0 F1 : CNF Nat} {s : PlainState}
    (hF : F1.Entails F0) (h : WatchesInv c F0 s) : WatchesInv c F1 s :=
  ⟨h.bounds, fun l hl => (h.slices l hl).mono hF (fun _ hr => hr) (fun _ _ _ => rfl)⟩

/-! ## 3. Core CDCL trail, three-way reason, and minimization invariants -/

/-- Mark-agnostic core CDCL trail & reason invariant for `D-Plain` (`independent of PlainHeur`).
`rsns[p / 2]` supports:
- `0xFFFFFFFF#32` (decision or flushed level-0 unit),
- binary watch reason `(rsn &&& 0x80000000#32) ≠ 0#32` (`ot = (rsn &&& 0x7FFFFFFF#32).toNat`),
- large arena clause ref `rsn.toNat < 0x80000000` (`rsn.toNat ∈ arenaClauseRefs s`, live). -/
structure PlainCoreInv (c : PlainCfg) (F0 : CNF Nat) (s : PlainState) : Prop where
  lengths : s.LengthsOk c
  arena : ArenaClausesInv c F0 s
  watches : WatchesInv c F0 s
  cur_level_le : s.cur_level ≤ s.trail_end
  trail_lits_lt : ∀ i < s.trail_end, (s.trl[i]?.getD 0#32).toNat < 2 * c.mv
  trail_vars_nodup : ∀ i j, i < s.trail_end → j < s.trail_end →
    (s.trl[i]?.getD 0#32).toNat / 2 = (s.trl[j]?.getD 0#32).toNat / 2 → i = j
  vals_domain : ∀ l < 2 * c.mv,
    s.vals[l]?.getD 0#8 = 0#8 ∨ s.vals[l]?.getD 0#8 = 1#8 ∨ s.vals[l]?.getD 0#8 = 0xFF#8
  vals_true_iff : ∀ l < 2 * c.mv,
    s.vals[l]?.getD 0#8 = 1#8 ↔ ∃ i < s.trail_end, (s.trl[i]?.getD 0#32).toNat = l
  vals_false_iff : ∀ l < 2 * c.mv,
    s.vals[l]?.getD 0#8 = 0xFF#8 ↔ ∃ i < s.trail_end, (s.trl[i]?.getD 0#32).toNat = l ^^^ 1
  lvl_le : ∀ i < s.trail_end,
    (s.lvl[(s.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ s.cur_level
  trail_mono : ∀ i j, i ≤ j → j < s.trail_end →
    (s.lvl[(s.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
    (s.lvl[(s.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
  levels_inhabited : ∀ L, 1 ≤ L → L ≤ s.cur_level →
    ∃ i < s.trail_end, (s.lvl[(s.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = L
  level0_sound : ∀ i < s.trail_end,
    (s.lvl[(s.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 →
    F0.EntailsClause (cnfClause [(s.trl[i]?.getD 0#32).toNat])
  reason_inv : ∀ idx < s.trail_end,
    let p := (s.trl[idx]?.getD 0#32).toNat
    let rsn := s.rsns[p / 2]?.getD 0xFFFFFFFF#32
    rsn ≠ 0xFFFFFFFF#32 →
      if (rsn &&& 0x80000000#32) ≠ 0#32 then
        let ot := (rsn &&& 0x7FFFFFFF#32).toNat
        ot < 2 * c.mv ∧
        F0.EntailsClause (cnfClause [p, ot]) ∧
        ∃ k < idx, (s.trl[k]?.getD 0#32).toNat = ot ^^^ 1
      else
        rsn.toNat ∈ arenaClauseRefs s ∧
        arenaClauseGarb s rsn.toNat = false ∧
        ∀ q ∈ arenaClauseLits s rsn.toNat,
          q = p ∨ ∃ k < idx, (s.trl[k]?.getD 0#32).toNat = q ^^^ 1

abbrev PlainTrailInv := PlainCoreInv

/-- All entries of `s.mrk[0 ..< c.mv)` are zero. -/
def MarksClear (c : PlainCfg) (s : PlainState) : Prop :=
  ∀ v < c.mv, s.mrk[v]?.getD 0#8 = 0#8

/-- Iterative minimization mark invariant for `plain_min_lit` / `plain_shrink_blk` /
`plain_min_shrink` supporting binary and large arena reasons. -/
structure PlainMinMarkInv (c : PlainCfg) (F0 : CNF Nat) (s : PlainState)
    (keep : List Nat) : Prop where
  mrk_dom : ∀ v < c.mv,
    s.mrk[v]?.getD 0#8 = 0#8 ∨ s.mrk[v]?.getD 0#8 = 2#8 ∨ s.mrk[v]?.getD 0#8 = 4#8
  clr_cov : s.min_clr_full = 0#64 → ∀ v < c.mv, s.mrk[v]?.getD 0#8 ≠ 0#8 →
    ∃ k < s.min_clr_len, (s.min_clr[k]?.getD 0#32).toNat = v
  rem_sound : ∀ idx < s.trail_end,
    let p := (s.trl[idx]?.getD 0#32).toNat
    let v := p / 2
    s.mrk[v]?.getD 0#8 = 2#8 →
    (p ^^^ 1) ∈ keep ∨
      let rsn := s.rsns[v]?.getD 0xFFFFFFFF#32
      rsn ≠ 0xFFFFFFFF#32 ∧
      if (rsn &&& 0x80000000#32) ≠ 0#32 then
        let ot := (rsn &&& 0x7FFFFFFF#32).toNat
        ot < 2 * c.mv ∧
        F0.EntailsClause (cnfClause [p, ot]) ∧
        ∃ k < idx,
          (s.trl[k]?.getD 0#32).toNat = ot ^^^ 1 ∧
          ((s.lvl[ot / 2]?.getD 0#32).toNat = 0 ∨ s.mrk[ot / 2]?.getD 0#8 = 2#8)
      else
        rsn.toNat ∈ arenaClauseRefs s ∧
        arenaClauseGarb s rsn.toNat = false ∧
        ∀ q ∈ arenaClauseLits s rsn.toNat,
          q = p ∨
          ∃ k < idx,
            (s.trl[k]?.getD 0#32).toNat = q ^^^ 1 ∧
            ((s.lvl[q / 2]?.getD 0#32).toNat = 0 ∨ s.mrk[q / 2]?.getD 0#8 = 2#8)

/-- Full CDCL solver invariant (`PlainCoreInv` + `MarksClear`). -/
structure PlainInv (c : PlainCfg) (F0 : CNF Nat) (s : PlainState) : Prop where
  core : PlainCoreInv c F0 s
  marks : MarksClear c s

/-! ## 4. Invariant preservation & minimization soundness lemmas -/

theorem PlainState.LengthsOk.with_heur {c : PlainCfg} {s : PlainState}
    (hlen : s.LengthsOk c) {heur' : PlainHeur} (hok : heur'.LengthsOk c) :
    ({ s with heur := heur' } : PlainState).LengthsOk c :=
  { hlen with heur_ok := hok }

theorem PlainCoreInv.mono {c : PlainCfg} {F0 F1 : CNF Nat} {s : PlainState}
    (hF : F1.Entails F0) (h : PlainCoreInv c F0 s) : PlainCoreInv c F1 s :=
  { h with
    arena := h.arena.mono hF
    watches := h.watches.mono hF
    level0_sound := fun i hi hl0 => CNF.entails_clause_trans hF (h.level0_sound i hi hl0)
    reason_inv := fun idx hidx hne => by
      dsimp only at hne ⊢
      have hr := h.reason_inv idx hidx hne
      split at hr <;> split
      · exact ⟨hr.1, CNF.entails_clause_trans hF hr.2.1, hr.2.2⟩
      · rename_i h1 h2; exact absurd h1 h2
      · rename_i h1 h2; exact absurd h2 h1
      · exact hr }

theorem PlainInv.mono {c : PlainCfg} {F0 F1 : CNF Nat} {s : PlainState}
    (hF : F1.Entails F0) (h : PlainInv c F0 s) : PlainInv c F1 s :=
  ⟨h.core.mono hF, h.marks⟩

theorem WatchesInv.with_wstk {c : PlainCfg} {F0 : CNF Nat} {s s' : PlainState}
    (h : WatchesInv c F0 s) (hw : s'.wvec = s.wvec) (hs : s'.wstk = s.wstk)
    (hl : s'.wlen = s.wlen) (ha : arenaClauseRefs s' = arenaClauseRefs s) :
    WatchesInv c F0 s' := by
  refine ⟨fun l hl' => by unfold watchOff watchSize; rw [hw, hl]; exact h.bounds l hl', ?_⟩
  intro l hl'
  simpa [watchOff, watchSize, hw] using
    (h.slices l hl').mono (by rw [CNF.entails_def]; exact fun _ h => h)
      (fun r hr => ha ▸ hr) (fun _ _ _ => by simp [hs])

theorem PlainCoreInv.with_heur {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (h : PlainCoreInv c F0 s) {heur' : PlainHeur} (hok : heur'.LengthsOk c) :
    PlainCoreInv c F0 { s with heur := heur' } :=
  { h with
    lengths := h.lengths.with_heur hok
    arena := { h.arena with len_ok := h.arena.len_ok }
    watches := h.watches.with_wstk rfl rfl rfl rfl }

theorem PlainInv.with_heur {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (h : PlainInv c F0 s) {heur' : PlainHeur} (hok : heur'.LengthsOk c) :
    PlainInv c F0 { s with heur := heur' } :=
  ⟨h.core.with_heur hok, h.marks⟩

theorem PlainCoreInv.with_d {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (h : PlainCoreInv c F0 s) (cur' val' : BitVec 64) :
    PlainCoreInv c F0 { s with d_cur := cur', d_val := val' } :=
  { h with
    lengths := { h.lengths with vals_len := h.lengths.vals_len }
    arena := { h.arena with len_ok := h.arena.len_ok }
    watches := h.watches.with_wstk rfl rfl rfl rfl }

theorem PlainInv.with_d {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (h : PlainInv c F0 s) (cur' val' : BitVec 64) :
    PlainInv c F0 { s with d_cur := cur', d_val := val' } :=
  ⟨h.core.with_d cur' val', h.marks⟩

theorem PlainCoreInv.vals_zero_iff {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (h : PlainCoreInv c F0 s) {l : Nat} (hl : l < 2 * c.mv) :
    s.vals[l]?.getD 0#8 = 0#8 ↔ ∀ i < s.trail_end, (s.trl[i]?.getD 0#32).toNat / 2 ≠ l / 2 := by
  constructor
  · intro hz i hi hvar
    rcases (litVar_eq_iff _ l).mp hvar with h1 | h2
    · have ht := (h.vals_true_iff l hl).mpr ⟨i, hi, h1⟩; rw [hz] at ht; cases ht
    · have hf := (h.vals_false_iff l hl).mpr ⟨i, hi, h2⟩; rw [hz] at hf; cases hf
  · intro hnone
    rcases h.vals_domain l hl with h0 | h1 | h2
    · exact h0
    · obtain ⟨i, hi, heq⟩ := (h.vals_true_iff l hl).mp h1
      exact absurd (by rw [heq]) (hnone i hi)
    · obtain ⟨i, hi, heq⟩ := (h.vals_false_iff l hl).mp h2
      have hvar : (l ^^^ 1) / 2 = l / 2 := litVar_litNeg l
      exact absurd (by rw [heq, hvar]) (hnone i hi)

theorem PlainCoreInv.trail_end_lt_of_unassigned {c : PlainCfg} {F0 : CNF Nat}
    {s : PlainState} (h : PlainCoreInv c F0 s) {l : Nat} (hl : l < 2 * c.mv)
    (hun : s.vals[l]?.getD 0#8 = 0#8) : s.trail_end < c.mv := by
  have hmiss := (h.vals_zero_iff hl).mp hun
  exact inj_lt_of_missing (fun i => (s.trl[i]?.getD 0#32).toNat / 2)
    (fun i j hi hj heq => h.trail_vars_nodup i j hi hj heq)
    (fun i hi => by have := h.trail_lits_lt i hi; omega)
    (by omega : l / 2 < c.mv) hmiss

theorem PlainCoreInv.level0_unsat_of_bin_conflict {c : PlainCfg} {F0 : CNF Nat}
    {s : PlainState} (h : PlainCoreInv c F0 s) (hl0 : s.cur_level = 0)
    {l0 l1 : Nat} (h0lt : l0 < 2 * c.mv) (h1lt : l1 < 2 * c.mv)
    (hent : F0.EntailsClause (cnfClause [l0, l1]))
    (hf0 : s.vals[l0]?.getD 0#8 = 0xFF#8) (hf1 : s.vals[l1]?.getD 0#8 = 0xFF#8) : F0.Unsat := by
  have hnil : F0.EntailsClause (cnfClause []) := by
    refine entails_of_mem_or_false hent fun l hl => Or.inr ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · obtain ⟨i, hi, hieq⟩ := (h.vals_false_iff l h0lt).mp hf0
      have hli : (s.lvl[(s.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
        have := h.lvl_le i hi; omega
      have hs := h.level0_sound i hi hli; rwa [hieq] at hs
    · obtain ⟨i, hi, hieq⟩ := (h.vals_false_iff l h1lt).mp hf1
      have hli : (s.lvl[(s.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
        have := h.lvl_le i hi; omega
      have hs := h.level0_sound i hi hli; rwa [hieq] at hs
  exact unsat_of_entails_nil hnil

theorem PlainCoreInv.level0_unsat_of_conflict {c : PlainCfg} {F0 : CNF Nat}
    {s : PlainState} (h : PlainCoreInv c F0 s) (hl0 : s.cur_level = 0)
    {cref : Nat} (href : cref ∈ arenaClauseRefs s) (hg : arenaClauseGarb s cref = false)
    (hfals : ∀ l ∈ arenaClauseLits s cref, s.vals[l]?.getD 0#8 = 0xFF#8) : F0.Unsat := by
  have hent := h.arena.entails cref href hg
  have hnil : F0.EntailsClause (cnfClause []) := by
    refine entails_of_mem_or_false hent fun l hl => Or.inr ?_
    have hlt := h.arena.lits_lt cref href hg l hl
    obtain ⟨i, hi, hieq⟩ := (h.vals_false_iff l hlt).mp (hfals l hl)
    have hli : (s.lvl[(s.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
      have := h.lvl_le i hi; omega
    have hs := h.level0_sound i hi hli
    rwa [hieq] at hs
  exact unsat_of_entails_nil hnil

theorem PlainCoreInv.falsified_lit_unique {c : PlainCfg} {F0 : CNF Nat}
    {s : PlainState} (h : PlainCoreInv c F0 s) {l1 l2 : Nat}
    (hl1 : l1 < 2 * c.mv) (hl2 : l2 < 2 * c.mv) (hv : l1 / 2 = l2 / 2)
    (hf1 : s.vals[l1]?.getD 0#8 = 0xFF#8) (hf2 : s.vals[l2]?.getD 0#8 = 0xFF#8) :
    l1 = l2 := by
  obtain ⟨i1, hi1, he1⟩ := (h.vals_false_iff l1 hl1).mp hf1
  obtain ⟨i2, hi2, he2⟩ := (h.vals_false_iff l2 hl2).mp hf2
  have hi : i1 = i2 := h.trail_vars_nodup i1 i2 hi1 hi2 (by
    rw [he1, he2]
    have h1 := litVar_litNeg l1; have h2 := litVar_litNeg l2
    unfold litVar litNeg at h1 h2; omega)
  subst hi
  have hx : litNeg l1 = litNeg l2 := he1.symm.trans he2
  simpa using congrArg litNeg hx

/-- Pushing an unassigned literal onto the trail (`plain_assign`) preserves `PlainCoreInv`. -/
theorem assign_preserves_core {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (hinv : PlainCoreInv c F0 s) {lit rsn : BitVec 32} {phases' : List (BitVec 8)}
    {unflushed' : BitVec 64}
    (hlit : lit.toNat < 2 * c.mv) (hph : phases'.length = c.mv)
    (hun : s.vals[lit.toNat]?.getD 0#8 = 0#8)
    (hcur_le : s.cur_level ≤ s.trail_end + 1)
    (hinhab : ∀ L, 1 ≤ L → L ≤ s.cur_level →
      L = s.cur_level ∨
        ∃ i < s.trail_end, (s.lvl[(s.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = L)
    (hl0 : s.cur_level = 0 → F0.EntailsClause (cnfClause [lit.toNat]))
    (hrsn : s.cur_level ≠ 0 → rsn ≠ 0xFFFFFFFF#32 →
      if (rsn &&& 0x80000000#32) ≠ 0#32 then
        let ot := (rsn &&& 0x7FFFFFFF#32).toNat
        ot < 2 * c.mv ∧ F0.EntailsClause (cnfClause [lit.toNat, ot]) ∧
        ∃ k < s.trail_end, (s.trl[k]?.getD 0#32).toNat = ot ^^^ 1
      else
        rsn.toNat ∈ arenaClauseRefs s ∧ arenaClauseGarb s rsn.toNat = false ∧
        ∀ q ∈ arenaClauseLits s rsn.toNat,
          q = lit.toNat ∨ ∃ k < s.trail_end, (s.trl[k]?.getD 0#32).toNat = q ^^^ 1) :
    let v := lit.toNat / 2
    let rsn' := if s.cur_level = 0 then 0xFFFFFFFF#32 else rsn
    let s' : PlainState :=
      { s with
        vals := (s.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
        lvl := s.lvl.set v (BitVec.ofNat 32 s.cur_level)
        rsns := s.rsns.set v rsn'
        trl := s.trl.set s.trail_end lit
        trail_pos := s.trail_pos.set v (BitVec.ofNat 32 s.trail_end)
        trail_end := s.trail_end + 1
        unflushed := unflushed'
        heur := { s.heur with phases := phases' } }
    PlainCoreInv c F0 s' := by
  intro v rsn' s'
  have hte_lt : s.trail_end < c.mv := hinv.trail_end_lt_of_unassigned hlit hun
  have hnot_var : ∀ i < s.trail_end, (s.trl[i]?.getD 0#32).toNat / 2 ≠ v :=
    (hinv.vals_zero_iff hlit).mp hun
  have hnlit_lt : (lit.toNat ^^^ 1) < 2 * c.mv := litNeg_lt_two_mul hlit
  have hne_lit : lit.toNat ^^^ 1 ≠ lit.toNat := litNeg_ne_self lit.toNat
  have hlen := hinv.lengths
  have hcur_lt32 : s.cur_level < 2 ^ 32 := by
    have := c.hmv; unfold dimacsBound at this
    have := hinv.cur_level_le; have := hlen.trail_end_le; omega
  have htrl_get : ∀ i < s.trail_end + 1,
      (s'.trl[i]?.getD 0#32).toNat =
        if i = s.trail_end then lit.toNat else (s.trl[i]?.getD 0#32).toNat := by
    intro i hi
    by_cases he : i = s.trail_end
    · subst he; simp [s', List.getElem?_set_self (by rw [hlen.trl_len]; omega)]
    · simp [s', he, List.getElem?_set_ne (Ne.symm he)]
  have hlvl_get : ∀ w < c.mv,
      (s'.lvl[w]?.getD 0#32).toNat =
        if w = v then s.cur_level else (s.lvl[w]?.getD 0#32).toNat := by
    intro w hw
    by_cases he : w = v
    · subst he
      simp [s', List.getElem?_set_self (by rw [hlen.lvl_len]; omega), bv32_ofNat_toNat hcur_lt32]
    · simp [s', he, List.getElem?_set_ne (Ne.symm he)]
  have hvals_get : ∀ l < 2 * c.mv,
      s'.vals[l]?.getD 0#8 =
        if l = lit.toNat ^^^ 1 then 0xFF#8
        else if l = lit.toNat then 1#8
        else s.vals[l]?.getD 0#8 := by
    intro l hl
    by_cases h1 : l = lit.toNat ^^^ 1
    · subst h1; dsimp only [s']; simp only [↓reduceIte]
      rw [List.getElem?_set_self (by simp [hlen.vals_len]; exact hnlit_lt)]; rfl
    · dsimp only [s']; simp only [h1, ↓reduceIte]
      rw [List.getElem?_set_ne (Ne.symm h1)]
      by_cases h2 : l = lit.toNat
      · subst h2; simp only [↓reduceIte]
        rw [List.getElem?_set_self (by rw [hlen.vals_len]; exact hlit)]; rfl
      · simp only [h2, ↓reduceIte]; rw [List.getElem?_set_ne (Ne.symm h2)]
  have hs'_te : s'.trail_end = s.trail_end + 1 := rfl
  have hs'_cl : s'.cur_level = s.cur_level := rfl
  have hs'_arena : ArenaClausesInv c F0 s' :=
    { hinv.arena with len_ok := hinv.arena.len_ok }
  have hs'_watches : WatchesInv c F0 s' :=
    hinv.watches.with_wstk rfl rfl rfl rfl
  have hlen' : s'.LengthsOk c :=
    { hlen with
      vals_len := by simp [s', hlen.vals_len]
      lvl_len := by simp [s', hlen.lvl_len]
      rsns_len := by simp [s', hlen.rsns_len]
      trl_len := by simp [s', hlen.trl_len]
      trail_pos_len := by simp [s', hlen.trail_pos_len]
      trail_end_le := by dsimp [s']; omega
      propagated_le := by dsimp [s']; have := hlen.propagated_le; omega
      heur_ok := { hlen.heur_ok with phases_len := hph } }
  refine ⟨hlen', hs'_arena, hs'_watches, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi; rw [hs'_te] at hi; rw [htrl_get i hi]; split
    · exact hlit
    · exact hinv.trail_lits_lt i (by omega)
  · intro i j hi hj hveq; rw [hs'_te] at hi hj; rw [htrl_get i hi, htrl_get j hj] at hveq
    split at hveq <;> split at hveq
    · omega
    · exact absurd hveq.symm (hnot_var j (by omega))
    · exact absurd hveq (hnot_var i (by omega))
    · exact hinv.trail_vars_nodup i j (by omega) (by omega) hveq
  · intro l hl; rw [hvals_get l hl]
    split; · exact Or.inr (Or.inr rfl)
    split; · exact Or.inr (Or.inl rfl)
    exact hinv.vals_domain l hl
  · intro l hl; rw [hvals_get l hl, hs'_te]
    constructor
    · intro h1
      by_cases hneg : l = lit.toNat ^^^ 1
      · simp [hneg] at h1
      · simp only [hneg, ↓reduceIte] at h1
        by_cases hpos : l = lit.toNat
        · exact ⟨s.trail_end, by omega, by rw [htrl_get _ (by omega)]; simp [hpos]⟩
        · simp only [hpos, ↓reduceIte] at h1
          obtain ⟨i, hi, heq⟩ := (hinv.vals_true_iff l hl).mp h1
          exact ⟨i, by omega,
            by rw [htrl_get i (by omega)]; simp [show i ≠ s.trail_end by omega, heq]⟩
    · rintro ⟨i, hi, heq⟩; rw [htrl_get i hi] at heq
      by_cases hie : i = s.trail_end
      · simp only [hie, ↓reduceIte] at heq; subst heq; simp [Ne.symm hne_lit]
      · simp only [hie, ↓reduceIte] at heq
        have hlv : l / 2 ≠ v := by rw [← heq]; exact hnot_var i (by omega)
        have h1 : l ≠ lit.toNat ^^^ 1 := fun h => hlv (by rw [h]; exact litVar_litNeg _)
        have h2 : l ≠ lit.toNat := fun h => hlv (by rw [h])
        simp only [h1, h2, ↓reduceIte]; exact (hinv.vals_true_iff l hl).mpr ⟨i, by omega, heq⟩
  · intro l hl; rw [hvals_get l hl, hs'_te]
    constructor
    · intro h1
      by_cases hneg : l = lit.toNat ^^^ 1
      · exact ⟨s.trail_end, by omega, by
          rw [htrl_get _ (by omega)]; simp only [↓reduceIte, hneg]; exact (litNeg_litNeg _).symm⟩
      · simp only [hneg, ↓reduceIte] at h1
        by_cases hpos : l = lit.toNat
        · simp [hpos] at h1
        · simp only [hpos, ↓reduceIte] at h1
          obtain ⟨i, hi, heq⟩ := (hinv.vals_false_iff l hl).mp h1
          exact ⟨i, by omega,
            by rw [htrl_get i (by omega)]; simp [show i ≠ s.trail_end by omega, heq]⟩
    · rintro ⟨i, hi, heq⟩; rw [htrl_get i hi] at heq
      by_cases hie : i = s.trail_end
      · simp only [hie, ↓reduceIte] at heq
        have hl_eq : l = lit.toNat ^^^ 1 := by
          have h := congrArg litNeg heq
          have h1 : litNeg (l ^^^ 1) = l := litNeg_litNeg l
          rw [h1] at h; exact h.symm
        simp [hl_eq]
      · simp only [hie, ↓reduceIte] at heq
        have hlv : l / 2 ≠ v := by
          have h := hnot_var i (by omega); rw [heq] at h
          rwa [show (l ^^^ 1) / 2 = l / 2 from litVar_litNeg l] at h
        have h1 : l ≠ lit.toNat ^^^ 1 := fun h => hlv (by rw [h]; exact litVar_litNeg _)
        have h2 : l ≠ lit.toNat := fun h => hlv (by rw [h])
        simp only [h1, h2, ↓reduceIte]; exact (hinv.vals_false_iff l hl).mpr ⟨i, by omega, heq⟩
  · intro i hi; rw [hs'_te] at hi; rw [hs'_cl, htrl_get i hi]
    by_cases hie : i = s.trail_end
    · simp only [hie, ↓reduceIte]; rw [hlvl_get v (by omega)]; simp
    · have hilt : i < s.trail_end := by omega
      simp only [hie, ↓reduceIte]
      rw [hlvl_get _ (by have := hinv.trail_lits_lt i hilt; omega)]
      simp only [hnot_var i hilt, ↓reduceIte]; exact hinv.lvl_le i hilt
  · intro i j hij hj; rw [hs'_te] at hj; rw [htrl_get i (by omega), htrl_get j hj]
    by_cases hje : j = s.trail_end
    · simp only [hje, ↓reduceIte]; rw [hlvl_get v (by omega)]; simp only [↓reduceIte]
      by_cases hie : i = s.trail_end
      · simp only [hie, ↓reduceIte]; rw [hlvl_get v (by omega)]; simp
      · have hilt : i < s.trail_end := by omega
        simp only [hie, ↓reduceIte]
        rw [hlvl_get _ (by have := hinv.trail_lits_lt i hilt; omega)]
        simp only [hnot_var i hilt, ↓reduceIte]; exact hinv.lvl_le i hilt
    · have hjlt : j < s.trail_end := by omega
      have hilt : i < s.trail_end := by omega
      simp only [show i ≠ s.trail_end by omega, hje, ↓reduceIte]
      rw [hlvl_get _ (by have := hinv.trail_lits_lt i hilt; omega),
        hlvl_get _ (by have := hinv.trail_lits_lt j hjlt; omega)]
      simp only [hnot_var i hilt, hnot_var j hjlt, ↓reduceIte]
      exact hinv.trail_mono i j hij hjlt
  · intro L hL1 hLle; rw [hs'_cl] at hLle; rw [hs'_te]
    rcases hinhab L hL1 hLle with rfl | ⟨i, hi, hli⟩
    · refine ⟨s.trail_end, by omega, ?_⟩
      rw [htrl_get _ (by omega)]; simp only [↓reduceIte]; rw [hlvl_get v (by omega)]; simp
    · refine ⟨i, by omega, ?_⟩
      rw [htrl_get i (by omega)]; simp only [show i ≠ s.trail_end by omega, ↓reduceIte]
      rw [hlvl_get _ (by have := hinv.trail_lits_lt i hi; omega)]
      simp [hnot_var i hi, hli]
  · intro i hi hli; rw [hs'_te] at hi; rw [htrl_get i hi] at hli ⊢
    by_cases hie : i = s.trail_end
    · simp only [hie, ↓reduceIte] at hli ⊢
      rw [hlvl_get v (by omega)] at hli; simp only [↓reduceIte] at hli; exact hl0 hli
    · have hilt : i < s.trail_end := by omega
      simp only [hie, ↓reduceIte] at hli ⊢
      rw [hlvl_get _ (by have := hinv.trail_lits_lt i hilt; omega)] at hli
      simp only [hnot_var i hilt, ↓reduceIte] at hli; exact hinv.level0_sound i hilt hli
  · intro idx hidx; rw [hs'_te] at hidx; dsimp only; rw [htrl_get idx hidx]
    by_cases hie : idx = s.trail_end
    · simp only [hie, ↓reduceIte]
      have hr : s'.rsns[v]?.getD 0xFFFFFFFF#32 = rsn' := by
        dsimp only [s']; rw [List.getElem?_set_self (by rw [hlen.rsns_len]; omega)]; rfl
      rw [hr]; intro hne
      by_cases hcl0 : s.cur_level = 0
      · simp [rsn', hcl0] at hne
      · have hrs := hrsn hcl0 (by simpa [rsn', hcl0] using hne)
        simp only [rsn', hcl0, ↓reduceIte] at hne hrs ⊢
        split at hrs <;> split
        · obtain ⟨k, hk, hkeq⟩ := hrs.2.2
          exact ⟨hrs.1, hrs.2.1, ⟨k, hk, by
            rw [htrl_get k (by omega)]; simp [show k ≠ s.trail_end by omega, hkeq]⟩⟩
        · rename_i h1 h2; exact absurd h1 h2
        · rename_i h1 h2; exact absurd h2 h1
        · refine ⟨hrs.1, hrs.2.1, fun q hq => ?_⟩
          have hq' : q ∈ arenaClauseLits s rsn.toNat := by
            simpa [arenaClauseLits, arenaClauseSize, s'] using hq
          exact (hrs.2.2 q hq').elim Or.inl fun ⟨k, hk, hkeq⟩ => Or.inr ⟨k, hk, by
            rw [htrl_get k (by omega)]; simp [show k ≠ s.trail_end by omega, hkeq]⟩
    · simp only [hie, ↓reduceIte]
      have hilt : idx < s.trail_end := by omega
      have hnv : (s.trl[idx]?.getD 0#32).toNat / 2 ≠ v := hnot_var idx hilt
      have hr : s'.rsns[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 =
          s.rsns[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 := by
        simp [s', List.getElem?_set_ne (Ne.symm hnv)]
      rw [hr]; intro hne; have hrs := hinv.reason_inv idx hilt hne
      split at hrs <;> split
      · obtain ⟨k, hk, hkeq⟩ := hrs.2.2
        exact ⟨hrs.1, hrs.2.1, ⟨k, hk, by
          rw [htrl_get k (by omega)]; simp [show k ≠ s.trail_end by omega, hkeq]⟩⟩
      · rename_i h1 h2; exact absurd h1 h2
      · rename_i h1 h2; exact absurd h2 h1
      · refine ⟨hrs.1, hrs.2.1, fun q hq => ?_⟩
        have hq' : q ∈ arenaClauseLits s
            (s.rsns[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat := by
          simpa [arenaClauseLits, arenaClauseSize, s'] using hq
        exact (hrs.2.2 q hq').elim Or.inl fun ⟨k, hk, hkeq⟩ => Or.inr ⟨k, hk, by
          rw [htrl_get k (by omega)]; simp [show k ≠ s.trail_end by omega, hkeq]⟩

/-- Helper state update after appending one large clause (`len ≥ 3`) in `plain_add_clause`. -/
def addClauseState (s : PlainState) (len : Nat) (arena' wvec' wstk' : List (BitVec 32))
    (wlen' : Nat) (wusable' fred' ni' nr' : BitVec 64)
    (wsort' : List (BitVec 32)) : PlainState :=
  { s with
    arena_len := s.arena_len + 3 + len
    wlen := wlen'
    wusable := wusable'
    first_reducible := fred'
    num_irred := ni'
    num_redundant := nr'
    wvec := wvec'
    arena := arena'
    wstk := wstk'
    heur := { s.heur with wsort := wsort' } }

/-- Appending an entailed clause of length `≥ 3` into the `COMPACT` `ward` arena preserves
`PlainCoreInv`. -/
theorem addClause_preserves_core {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    {len : Nat} {arena' wvec' wstk' wsort' : List (BitVec 32)}
    {wlen' : Nat} {wusable' fred' ni' nr' : BitVec 64}
    (hinv : PlainCoreInv c F0 s)
    (hlen' : (addClauseState s len arena' wvec' wstk'
      wlen' wusable' fred' ni' nr' wsort').LengthsOk c)
    (hge3 : 3 ≤ len)
    (hlits_lt : ∀ l ∈ (s.tmp.take len).map BitVec.toNat, l < 2 * c.mv)
    (hent : F0.EntailsClause (cnfClause ((s.tmp.take len).map BitVec.toNat)))
    (hhold_arena : ∀ k < s.arena_len, arena'[k]? = s.arena[k]?)
    (hnxt_hold : ∀ r ∈ arenaClauseRefs s,
      arenaNextOff arena' (s.arena_len + 3 + len) r = arenaNextOff s.arena s.arena_len r)
    (hnew_noshrk : (arena'[s.arena_len]?.getD 0#32 &&& 0x00800000#32) = 0#32)
    (hnew_nogarb : (arena'[s.arena_len]?.getD 0#32 &&& 0x00080000#32) = 0#32)
    (hnew_sz : (arena'[s.arena_len + 2]?.getD 0#32).toNat = len)
    (hnew_lits : arenaClauseLits
      (addClauseState s len arena' wvec' wstk' wlen' wusable' fred' ni' nr' wsort') s.arena_len =
      (s.tmp.take len).map BitVec.toNat)
    (hwat : WatchesInv c F0
      (addClauseState s len arena' wvec' wstk' wlen' wusable' fred' ni' nr' wsort')) :
    PlainCoreInv c F0
      (addClauseState s len arena' wvec' wstk' wlen' wusable' fred' ni' nr' wsort') := by
  let s' := addClauseState s len arena' wvec' wstk' wlen' wusable' fred' ni' nr' wsort'
  have hrefs : arenaClauseRefs s' = arenaClauseRefs s ++ [s.arena_len] := by
    unfold arenaClauseRefs s' addClauseState
    exact arenaScanRefs_eq_of_prefix hge3 hnew_noshrk hnew_sz
      (fun r hr => (hinv.arena.refs_wf r hr).2.2.2.2) hinv.arena.chain_end hnxt_hold
  have hold_garb : ∀ r ∈ arenaClauseRefs s, arenaClauseGarb s' r = arenaClauseGarb s r := by
    intro r hr
    have hr3 := (hinv.arena.refs_wf r hr).1
    unfold arenaClauseGarb arenaHdr s' addClauseState
    simp [hhold_arena r (by omega)]
  have hold_sz : ∀ r ∈ arenaClauseRefs s, arenaClauseSize s' r = arenaClauseSize s r := by
    intro r hr
    have hr3 := (hinv.arena.refs_wf r hr).1
    unfold arenaClauseSize s' addClauseState
    simp [hhold_arena (r + 2) (by omega)]
  have hold_lits : ∀ r ∈ arenaClauseRefs s, arenaClauseLits s' r = arenaClauseLits s r := by
    intro r hr
    have hwf := hinv.arena.refs_wf r hr
    have hle_a : s.arena_len ≤ s'.arena_len := by dsimp [s', addClauseState]; omega
    have h1l := hinv.lengths.arena_len_arr; have h1e := hinv.lengths.arena_len_le
    have h2l : s'.arena.length = c.arena_cap := hlen'.arena_len_arr
    have h2e : s'.arena_len ≤ c.arena_cap := hlen'.arena_len_le
    have hbd_ar : r + 3 + arenaClauseSize s r ≤ s.arena_len := by
      have h1 := hwf.2.2.1; have h2 := hwf.2.2.2.1; omega
    have hbd1 : r + 3 + arenaClauseSize s r ≤ s.arena.length := by omega
    have hbd2 : r + 3 + arenaClauseSize s r ≤ s'.arena.length := by omega
    dsimp only [s', addClauseState] at hbd2
    unfold arenaClauseLits; rw [hold_sz r hr]
    apply List.ext_getElem
    · simp only [List.length_map, List.length_take, List.length_drop]
      rw [Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]
    · intro k hk1 _
      simp only [List.getElem_map, List.getElem_take, List.getElem_drop]
      have hks : k < arenaClauseSize s r := by
        simp only [List.length_map, List.length_take, List.length_drop] at hk1; omega
      have heq := hhold_arena (r + 3 + k) (by omega)
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at heq
      exact congrArg BitVec.toNat (Option.some.inj heq)
  have hnew_sz_s' : arenaClauseSize s' s.arena_len = len := hnew_sz
  have hnew_garb_s' : arenaClauseGarb s' s.arena_len = false := by
    unfold arenaClauseGarb arenaHdr s' addClauseState; simp [hnew_nogarb]
  have harena' : ArenaClausesInv c F0 s' := by
    refine ⟨Or.inr (by dsimp [s', addClauseState]; omega), ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · have hwf := hinv.arena.refs_wf r hr
        have hnx : arenaNextOff s'.arena s'.arena_len r = arenaNextOff s.arena s.arena_len r :=
          hnxt_hold r hr
        rw [hnx, hold_sz r hr]
        refine ⟨by dsimp [s', addClauseState]; omega, hwf.2.1, hwf.2.2.1,
          by dsimp [s', addClauseState]; omega, ?_⟩
        rcases hwf.2.2.2.2 with he | h3 <;> right <;> dsimp [s', addClauseState] <;> omega
      · have hnxt_new : arenaNextOff s'.arena s'.arena_len s.arena_len = s.arena_len + 3 + len := by
          unfold arenaNextOff s' addClauseState; simp [hnew_sz, hnew_noshrk]
        rw [hnxt_new, hnew_sz_s']
        refine ⟨by dsimp [s', addClauseState]; omega, hge3, by omega,
          by dsimp [s', addClauseState]; omega, Or.inl (by dsimp [s', addClauseState])⟩
    · intro r hr hng; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · rw [hold_garb r hr] at hng; rw [hold_lits r hr]; exact hinv.arena.lits_lt r hr hng
      · rw [hnew_lits]; exact hlits_lt
    · intro r hr hng; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · rw [hold_garb r hr] at hng; rw [hold_lits r hr]; exact hinv.arena.entails r hr hng
      · rw [hnew_lits]; exact hent
  refine ⟨hlen', harena', hwat, hinv.cur_level_le, hinv.trail_lits_lt, hinv.trail_vars_nodup,
    hinv.vals_domain, hinv.vals_true_iff, hinv.vals_false_iff, hinv.lvl_le, hinv.trail_mono,
    hinv.levels_inhabited, hinv.level0_sound, ?_⟩
  intro idx hidx; dsimp only [s', addClauseState]; intro hne
  have hrs := hinv.reason_inv idx hidx hne
  split at hrs <;> split
  · exact hrs
  · rename_i h1 h2; exact absurd h1 h2
  · rename_i h1 h2; exact absurd h2 h1
  · have hrefs' := hrefs; have hgarb' := hold_garb _ hrs.1; have hlits' := hold_lits _ hrs.1
    dsimp only [s', addClauseState] at hrefs' hgarb' hlits'
    exact ⟨hrefs' ▸ List.mem_append_left _ hrs.1, hgarb'.trans hrs.2.1,
      fun q hq => hrs.2.2 q (hlits' ▸ hq)⟩

/-- Swapping two literals inside live arena clause `cref` + updating `ar[cref + 1]` and watches
preserves `PlainCoreInv`. -/
theorem swapCl_preserves_core {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (hinv : PlainCoreInv c F0 s) {cref k1 k2 : Nat} {srch : BitVec 32}
    {wvec' wstk' wsort' : List (BitVec 32)} {wlen' : Nat} {wusable' : BitVec 64}
    (hcref : cref ∈ arenaClauseRefs s)
    (hk1 : k1 < arenaClauseSize s cref) (hk2 : k2 < arenaClauseSize s cref)
    (hwvl : wvec'.length = 4 * c.mv) (hwsl : wstk'.length = c.wcap)
    (hwol : wsort'.length = 2 * c.mv) (hwle : wlen' ≤ c.wcap) :
    let hlen := hinv.lengths
    have hbd : cref + 3 + arenaClauseSize s cref ≤ s.arena.length := by
      have := (hinv.arena.refs_wf cref hcref).2.2.1
      have := (hinv.arena.refs_wf cref hcref).2.2.2.1
      have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
    let l1 := s.arena[cref + 3 + k1]'(by omega)
    let l2 := s.arena[cref + 3 + k2]'(by omega)
    let arena' := ((s.arena.set (cref + 1) srch).set (cref + 3 + k1) l2).set (cref + 3 + k2) l1
    let s' : PlainState :=
      { s with
        arena := arena', wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable',
        heur := { s.heur with wsort := wsort' } }
    WatchesInv c F0 s' → PlainCoreInv c F0 s' := by
  intro hlen hbd l1 l2 arena' s' hwat
  have hmc := hinv.arena.refs_wf cref hcref
  have har_set0 : arena'[cref]? = s.arena[cref]? := by
    simp only [arena']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega)]
  have har_set2 : arena'[cref + 2]? = s.arena[cref + 2]? := by
    simp only [arena']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega)]
  have har_eq_outside : ∀ i, (i < cref ∨ cref + 3 + arenaClauseSize s cref ≤ i) →
      arena'[i]? = s.arena[i]? := by
    intro i hi
    simp only [arena']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega)]
  have hnxt_eq : ∀ r ∈ arenaClauseRefs s,
      arenaNextOff s'.arena s.arena_len r = arenaNextOff s.arena s.arena_len r := by
    intro r hr
    by_cases hrc : r = cref
    · subst hrc
      refine arenaNextOff_congr_block har_set0 har_set2 fun k hk1' hk2' => ?_
      exact har_eq_outside k (Or.inr hk1')
    · rcases Nat.lt_or_gt_of_ne hrc with hlt | hgt
      · have hdisj := arenaScanRefs_disjoint hr hcref hlt
        have hr_bd := hinv.arena.refs_wf r hr
        refine arenaNextOff_congr_block
          (har_eq_outside r (Or.inl (by omega)))
          (har_eq_outside (r + 2) (Or.inl (by omega)))
          fun k hk1' hk2' => har_eq_outside k (Or.inl (by omega))
      · have hdisj := hinv.arena.disjoint hcref hr hgt
        refine arenaNextOff_congr_block
          (har_eq_outside r (Or.inr hdisj))
          (har_eq_outside (r + 2) (Or.inr (by omega)))
          fun k hk1' hk2' => har_eq_outside k (Or.inr (by omega))
  have hrefs : arenaClauseRefs s' = arenaClauseRefs s :=
    arenaClauseRefs_congr rfl hnxt_eq
  have hout_ref : ∀ r ∈ arenaClauseRefs s, r ≠ cref →
      r + 3 + arenaClauseSize s r ≤ cref ∨ cref + 3 + arenaClauseSize s cref ≤ r := by
    intro r hr hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl (hinv.arena.disjoint hr hcref hlt)
    · exact Or.inr (hinv.arena.disjoint hcref hr hgt)
  have hgarb_eq : ∀ r ∈ arenaClauseRefs s, arenaClauseGarb s' r = arenaClauseGarb s r := by
    intro r hr; unfold arenaClauseGarb arenaHdr; dsimp only [s']
    by_cases hrc : r = cref
    · subst r; rw [har_set0]
    · rcases hout_ref r hr hrc with hlt | hgt
      · rw [har_eq_outside r (Or.inl (by omega))]
      · rw [har_eq_outside r (Or.inr hgt)]
  have hsz_eq : ∀ r ∈ arenaClauseRefs s, arenaClauseSize s' r = arenaClauseSize s r := by
    intro r hr; unfold arenaClauseSize; dsimp only [s']
    by_cases hrc : r = cref
    · subst r; rw [har_set2]
    · rcases hout_ref r hr hrc with hlt | hgt
      · have h3 := (hinv.arena.refs_wf r hr).2.1; rw [har_eq_outside (r + 2) (Or.inl (by omega))]
      · rw [har_eq_outside (r + 2) (Or.inr (by omega))]
  have hswap_k : ∀ k (hk : k < arenaClauseSize s cref),
      s'.arena[cref + 3 + k]'(by simp [s', arena']; omega) =
        if k = k2 then l1 else if k = k1 then l2 else s.arena[cref + 3 + k]'(by omega) := by
    intro k hk; dsimp only [s', arena']
    by_cases hk2e : k = k2
    · subst k; simp [List.getElem_set_self]
    · simp only [hk2e, ↓reduceIte]
      rw [List.getElem_set_ne (by omega : cref + 3 + k2 ≠ cref + 3 + k)]
      by_cases hk1e : k = k1
      · subst k; simp [List.getElem_set_self]
      · simp only [hk1e, ↓reduceIte]
        rw [List.getElem_set_ne (by omega : cref + 3 + k1 ≠ cref + 3 + k),
          List.getElem_set_ne (by omega : cref + 1 ≠ cref + 3 + k)]
  have hmem_iff : ∀ r ∈ arenaClauseRefs s, ∀ l,
      l ∈ arenaClauseLits s' r ↔ l ∈ arenaClauseLits s r := by
    intro r hr l
    have hbd_r : r + 3 + arenaClauseSize s r ≤ s.arena.length := by
      have := (hinv.arena.refs_wf r hr).2.2.1; have := (hinv.arena.refs_wf r hr).2.2.2.1
      have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
    have hbd_r' : r + 3 + arenaClauseSize s' r ≤ s'.arena.length := by
      rw [hsz_eq r hr]; simp [s', arena', hbd_r]
    rw [mem_arenaClauseLits_iff hbd_r', mem_arenaClauseLits_iff hbd_r]
    simp only [hsz_eq r hr]
    by_cases hrc : r = cref
    · subst r
      constructor
      · rintro ⟨k, hk, hget⟩; rw [hswap_k k hk] at hget
        split at hget
        · exact ⟨k1, hk1, hget⟩
        · split at hget
          · exact ⟨k2, hk2, hget⟩
          · exact ⟨k, hk, hget⟩
      · rintro ⟨k, hk, hget⟩
        by_cases h1 : k = k1
        · subst k; refine ⟨k2, hk2, ?_⟩; rw [hswap_k k2 hk2]
          simp only [↓reduceIte]; dsimp only [l1]; exact hget
        · by_cases h2 : k = k2
          · subst k; refine ⟨k1, hk1, ?_⟩; rw [hswap_k k1 hk1]
            simp only [Ne.symm h1, ↓reduceIte]; dsimp only [l2]; exact hget
          · refine ⟨k, hk, ?_⟩; rw [hswap_k k hk]; simp only [h1, h2, ↓reduceIte]; exact hget
    · have hget_eq : ∀ k (hk : k < arenaClauseSize s r),
          s'.arena[r + 3 + k]'(by simp [s', arena']; omega) =
            s.arena[r + 3 + k]'(by omega) := fun k hk => by
        have hopt : s'.arena[r + 3 + k]? = s.arena[r + 3 + k]? := by
          dsimp only [s']
          rcases hout_ref r hr hrc with hlt | hgt
          · exact har_eq_outside (r + 3 + k) (Or.inl (by omega))
          · exact har_eq_outside (r + 3 + k) (Or.inr (by omega))
        rw [List.getElem?_eq_getElem (by simp [s', arena']; omega),
          List.getElem?_eq_getElem (by omega)] at hopt
        exact Option.some.inj hopt
      exact ⟨fun ⟨k, hk, h⟩ => ⟨k, hk, by rw [← hget_eq k hk]; exact h⟩,
        fun ⟨k, hk, h⟩ => ⟨k, hk, by rw [hget_eq k hk]; exact h⟩⟩
  have hlen' : s'.LengthsOk c :=
    { hlen with
      arena_len_arr := by simp [s', arena', hlen.arena_len_arr]
      wvec_len := hwvl, wstk_len_arr := hwsl, wlen_le := hwle
      heur_ok := { hlen.heur_ok with wsort_len := hwol } }
  have harena' : ArenaClausesInv c F0 s' := by
    refine ⟨hinv.arena.len_ok, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs] at hr; have hwf := hinv.arena.refs_wf r hr
      dsimp only [s']; rw [hnxt_eq r hr, hsz_eq r hr]; exact hwf
    · intro r hr hng l hl; rw [hrefs] at hr; rw [hgarb_eq r hr] at hng
      exact hinv.arena.lits_lt r hr hng l ((hmem_iff r hr l).mp hl)
    · intro r hr hng; rw [hrefs] at hr; rw [hgarb_eq r hr] at hng
      exact entails_of_mem_or_false (hinv.arena.entails r hr hng) fun l hl =>
        Or.inl ((hmem_iff r hr l).mpr hl)
  refine ⟨hlen', harena', hwat, hinv.cur_level_le, hinv.trail_lits_lt, hinv.trail_vars_nodup,
    hinv.vals_domain, hinv.vals_true_iff, hinv.vals_false_iff, hinv.lvl_le, hinv.trail_mono,
    hinv.levels_inhabited, hinv.level0_sound, ?_⟩
  intro idx hidx; dsimp only [s']; intro hne
  have hrs := hinv.reason_inv idx hidx hne
  split at hrs <;> split
  · exact hrs
  · rename_i h1 h2; exact absurd h1 h2
  · rename_i h1 h2; exact absurd h2 h1
  · exact ⟨hrefs ▸ hrs.1, (hgarb_eq _ hrs.1).trans hrs.2.1,
      fun q hq => hrs.2.2 q ((hmem_iff _ hrs.1 q).mp hq)⟩

/-- Initial zeroed state produced by `plain_init_state` satisfies `PlainInv`. -/
theorem plainInv_init {c : PlainCfg} {s : PlainState} (hlen : s.LengthsOk c)
    (hal : s.arena_len = 0) (hwvec : s.wvec = List.replicate (4 * c.mv) 0#32)
    (hte : s.trail_end = 0) (hcl : s.cur_level = 0)
    (hvals : s.vals = List.replicate (2 * c.mv) 0#8)
    (hmrk : s.mrk = List.replicate c.mv 0#8) :
    PlainInv c (shiftDownCnf CNF.empty) s := by
  have hrefs : arenaClauseRefs s = [] := by simp [arenaClauseRefs, hal, arenaScanRefs]
  have hw0 : ∀ l < 2 * c.mv, watchOff s l = 0 ∧ watchSize s l = 0 := fun l hl => by
    unfold watchOff watchSize; rw [hwvec]
    simp [show 2 * l < 4 * c.mv by omega, show 2 * l + 1 < 4 * c.mv by omega]
  exact ⟨⟨hlen,
    ⟨Or.inl hal,
     (by intro r hr; rw [hrefs] at hr; cases hr),
     (by intro r hr; rw [hrefs] at hr; cases hr),
     (by intro r hr; rw [hrefs] at hr; cases hr)⟩,
    ⟨fun l hl => by obtain ⟨ho, hs⟩ := hw0 l hl; omega,
     fun l hl => by obtain ⟨ho, hs⟩ := hw0 l hl; rw [ho, hs]; exact .empty⟩,
    by rw [hte, hcl]; exact Nat.le_refl _,
    fun _ h => by omega, fun _ _ h => by omega,
    fun l hl => by rw [hvals]; simp [hl], fun l hl => by rw [hvals, hte]; simp [hl],
    fun l hl => by rw [hvals, hte]; simp [hl],
    fun _ h => by omega, fun _ _ _ h => by omega,
    fun _ _ h2 => by omega, fun _ h => by omega, fun _ h => by omega⟩,
    fun v hv => by rw [hmrk]; simp [hv]⟩

theorem plainMinMarkInv_init {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (hcore : PlainCoreInv c F0 s) (hmc : MarksClear c s) (keep : List Nat) :
    PlainMinMarkInv c F0 s keep :=
  ⟨fun v hv => Or.inl (hmc v hv),
   fun _ v hv hnz => absurd (hmc v hv) hnz,
   fun idx hi h => by
     have hv : (s.trl[idx]?.getD 0#32).toNat / 2 < c.mv := by
       have := hcore.trail_lits_lt idx hi; omega
     have := hmc _ hv; rw [h] at this; cases this⟩

private theorem plain_trail_xor_var_lt {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (hcore : PlainCoreInv c F0 s) {k q : Nat} (hk : k < s.trail_end)
    (hkeq : (s.trl[k]?.getD 0#32).toNat = q ^^^ 1) : q / 2 < c.mv := by
  have hlt := hcore.trail_lits_lt k hk
  have hql : (q ^^^ 1) / 2 = q / 2 := litVar_litNeg q
  rw [hkeq, ← hql] at *; omega

/-- State update performed by `plain_min_mark(h, v, tag)` when `mrk[v] = 0`. -/
def plainMinMarkState (c : PlainCfg) (s : PlainState) (v : Nat) (tag : BitVec 8) :
    PlainState :=
  let mclr' := if s.min_clr_len < c.mv then s.min_clr.set s.min_clr_len (BitVec.ofNat 32 v)
               else s.min_clr
  let mcl' := if s.min_clr_len < c.mv then s.min_clr_len + 1 else s.min_clr_len
  let mcf' := if s.min_clr_len < c.mv then s.min_clr_full else 1#64
  { s with mrk := s.mrk.set v tag, min_clr := mclr', min_clr_len := mcl', min_clr_full := mcf' }

private theorem plain_clr_cov_mark_step {c : PlainCfg} {s : PlainState}
    (hcov : s.min_clr_full = 0#64 → ∀ w < c.mv, s.mrk[w]?.getD 0#8 ≠ 0#8 →
      ∃ k < s.min_clr_len, (s.min_clr[k]?.getD 0#32).toNat = w)
    {v : Nat} (hv : v < c.mv) (hmcll : s.min_clr.length = c.mv) (tag : BitVec 8) :
    let s' := plainMinMarkState c s v tag
    s'.min_clr_full = 0#64 → ∀ w < c.mv, s'.mrk[w]?.getD 0#8 ≠ 0#8 →
      ∃ k < s'.min_clr_len, (s'.min_clr[k]?.getD 0#32).toNat = w := by
  dsimp only [plainMinMarkState]
  intro hmcf w hw hnz
  by_cases hlt : s.min_clr_len < c.mv
  · simp only [hlt, ↓reduceIte] at hmcf hnz ⊢
    by_cases hweq : w = v
    · subst w
      refine ⟨s.min_clr_len, by omega, ?_⟩
      rw [List.getElem?_set_self (by omega), Option.getD_some,
        bv32_ofNat_toNat (by have := c.hmv; unfold dimacsBound at this; omega)]
    · have hnz' : s.mrk[w]?.getD 0#8 ≠ 0#8 := by
        simpa [List.getElem?_set_ne (Ne.symm hweq)] using hnz
      obtain ⟨k, hk, hkeq⟩ := hcov hmcf w hw hnz'
      exact ⟨k, by omega, by rw [List.getElem?_set_ne (by omega)]; exact hkeq⟩
  · simp only [hlt, ↓reduceIte] at hmcf; cases hmcf

private theorem plainMinMarkInv_lift_sound {c : PlainCfg} {F0 : CNF Nat}
    {s s' : PlainState} {keep : List Nat} (hcore : PlainCoreInv c F0 s)
    (hs_eq : s'.trail_end = s.trail_end ∧ s'.trl = s.trl ∧ s'.lvl = s.lvl ∧
      s'.rsns = s.rsns ∧ s'.arena = s.arena ∧ s'.arena_len = s.arena_len)
    (hmono : ∀ w < c.mv, s.mrk[w]?.getD 0#8 = 2#8 → s'.mrk[w]?.getD 0#8 = 2#8)
    (hprev : ∀ idx < s.trail_end,
      let p := (s.trl[idx]?.getD 0#32).toNat
      s.mrk[p / 2]?.getD 0#8 = 2#8 →
      (p ^^^ 1) ∈ keep ∨
        let rsn := s.rsns[p / 2]?.getD 0xFFFFFFFF#32
        rsn ≠ 0xFFFFFFFF#32 ∧
        if (rsn &&& 0x80000000#32) ≠ 0#32 then
          let ot := (rsn &&& 0x7FFFFFFF#32).toNat
          ot < 2 * c.mv ∧ F0.EntailsClause (cnfClause [p, ot]) ∧
          ∃ k < idx, (s.trl[k]?.getD 0#32).toNat = ot ^^^ 1 ∧
            ((s.lvl[ot / 2]?.getD 0#32).toNat = 0 ∨ s.mrk[ot / 2]?.getD 0#8 = 2#8)
        else
          rsn.toNat ∈ arenaClauseRefs s ∧ arenaClauseGarb s rsn.toNat = false ∧
          ∀ q ∈ arenaClauseLits s rsn.toNat,
            q = p ∨ ∃ k < idx, (s.trl[k]?.getD 0#32).toNat = q ^^^ 1 ∧
              ((s.lvl[q / 2]?.getD 0#32).toNat = 0 ∨ s.mrk[q / 2]?.getD 0#8 = 2#8))
    {idx : Nat} (hi : idx < s.trail_end)
    (h2' : s.mrk[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#8 = 2#8) :
    let p := (s'.trl[idx]?.getD 0#32).toNat
    (p ^^^ 1) ∈ keep ∨
      let rsn := s'.rsns[p / 2]?.getD 0xFFFFFFFF#32
      rsn ≠ 0xFFFFFFFF#32 ∧
      if (rsn &&& 0x80000000#32) ≠ 0#32 then
        let ot := (rsn &&& 0x7FFFFFFF#32).toNat
        ot < 2 * c.mv ∧ F0.EntailsClause (cnfClause [p, ot]) ∧
        ∃ k < idx, (s'.trl[k]?.getD 0#32).toNat = ot ^^^ 1 ∧
          ((s'.lvl[ot / 2]?.getD 0#32).toNat = 0 ∨ s'.mrk[ot / 2]?.getD 0#8 = 2#8)
      else
        rsn.toNat ∈ arenaClauseRefs s' ∧ arenaClauseGarb s' rsn.toNat = false ∧
        ∀ q ∈ arenaClauseLits s' rsn.toNat,
          q = p ∨ ∃ k < idx, (s'.trl[k]?.getD 0#32).toNat = q ^^^ 1 ∧
            ((s'.lvl[q / 2]?.getD 0#32).toNat = 0 ∨ s'.mrk[q / 2]?.getD 0#8 = 2#8) := by
  rcases hs_eq with ⟨_, htrl, hlvl, hrsn, har, hal⟩
  rw [htrl, hrsn, hlvl]
  have hr : arenaClauseRefs s' = arenaClauseRefs s := by simp [arenaClauseRefs, har, hal]
  have hcl : ∀ r, arenaClauseGarb s' r = arenaClauseGarb s r ∧
      arenaClauseLits s' r = arenaClauseLits s r := fun r => by
    simp [arenaClauseGarb, arenaHdr, arenaClauseLits, arenaClauseSize, har]
  rcases hprev idx hi h2' with hin | ⟨hne, hif⟩
  · exact Or.inl hin
  · refine Or.inr ⟨hne, ?_⟩
    split at hif <;> split
    · obtain ⟨hot, hent, k, hk, hkeq, hdep⟩ := hif
      exact ⟨hot, hent, k, hk, hkeq, hdep.elim Or.inl fun hk2 => Or.inr (hmono _ (by omega) hk2)⟩
    · rename_i h1 h2; exact absurd h1 h2
    · rename_i h1 h2; exact absurd h2 h1
    · obtain ⟨href, hng, hall⟩ := hif
      refine ⟨by rw [hr]; exact href, by rw [(hcl _).1]; exact hng, fun q hq => ?_⟩
      rw [(hcl _).2] at hq
      rcases hall q hq with rfl | ⟨k, hk, hkeq, hdep⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨k, hk, hkeq, hdep.elim Or.inl fun hk2 =>
          Or.inr (hmono _ (plain_trail_xor_var_lt hcore (Nat.lt_trans hk hi) hkeq) hk2)⟩

theorem plainMinMarkInv_poison {c : PlainCfg} {F0 : CNF Nat} {s : PlainState} {keep : List Nat}
    (hcore : PlainCoreInv c F0 s) (hmin : PlainMinMarkInv c F0 s keep)
    {v : Nat} (hv : v < c.mv) (hz : s.mrk[v]?.getD 0#8 = 0#8) :
    PlainMinMarkInv c F0 (plainMinMarkState c s v 4#8) keep := by
  let s' := plainMinMarkState c s v 4#8; change PlainMinMarkInv c F0 s' keep
  have hlen := hcore.lengths
  have hmono : ∀ w < c.mv, s'.mrk[w]?.getD 0#8 = 2#8 ↔ s.mrk[w]?.getD 0#8 = 2#8 := fun w _ => by
    by_cases hweq : w = v
    · subst w; rw [show s'.mrk[v]?.getD 0#8 = 4#8 by
        simp [s', plainMinMarkState, List.getElem?_set_self (by rw [hlen.mrk_len]; omega)], hz]
      decide
    · simp [s', plainMinMarkState, List.getElem?_set_ne (Ne.symm hweq)]
  refine ⟨fun w hw => ?_, plain_clr_cov_mark_step hmin.clr_cov hv hlen.min_clr_len_arr 4#8,
    fun idx hi h2 => ?_⟩
  · by_cases hweq : w = v
    · subst w; right; right
      simp [s', plainMinMarkState, List.getElem?_set_self (by rw [hlen.mrk_len]; omega)]
    · simp only [s', plainMinMarkState, List.getElem?_set_ne (Ne.symm hweq)]
      exact hmin.mrk_dom w hw
  · have hvw : (s.trl[idx]?.getD 0#32).toNat / 2 < c.mv := by
      have := hcore.trail_lits_lt idx hi; omega
    exact plainMinMarkInv_lift_sound (s' := s') hcore ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      (fun w hw => (hmono w hw).mpr) hmin.rem_sound hi ((hmono _ hvw).mp h2)

theorem plainMinMarkInv_mark_keep {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    {keep : List Nat} (hcore : PlainCoreInv c F0 s) (hmin : PlainMinMarkInv c F0 s keep)
    {l : Nat} (hl : l < 2 * c.mv) (hkeep : l ∈ keep) (hfals : s.vals[l]?.getD 0#8 = 0xFF#8)
    (hz : s.mrk[l / 2]?.getD 0#8 = 0#8) :
    PlainMinMarkInv c F0 (plainMinMarkState c s (l / 2) 2#8) keep := by
  let v := l / 2; let s' := plainMinMarkState c s v 2#8; change PlainMinMarkInv c F0 s' keep
  have hlen := hcore.lengths; have hv : v < c.mv := by omega
  have hmono : ∀ w < c.mv, s.mrk[w]?.getD 0#8 = 2#8 → s'.mrk[w]?.getD 0#8 = 2#8 := fun w _ hw2 => by
    by_cases hweq : w = v
    · subst w; rw [hz] at hw2; cases hw2
    · simp [s', plainMinMarkState, List.getElem?_set_ne (Ne.symm hweq), hw2]
  refine ⟨fun w hw => ?_, plain_clr_cov_mark_step hmin.clr_cov hv hlen.min_clr_len_arr 2#8,
    fun idx hi h2 => ?_⟩
  · by_cases hweq : w = v
    · subst w; right; left
      simp [s', plainMinMarkState, List.getElem?_set_self (by rw [hlen.mrk_len]; omega)]
    · simp only [s', plainMinMarkState, List.getElem?_set_ne (Ne.symm hweq)]
      exact hmin.mrk_dom w hw
  · have hi' : idx < s.trail_end := hi
    by_cases hveq : (s.trl[idx]?.getD 0#32).toNat / 2 = v
    · obtain ⟨k, hk, hkeq⟩ := (hcore.vals_false_iff l hl).mp hfals
      have hk_idx : k = idx := hcore.trail_vars_nodup k idx hk hi' (by
        rw [hkeq, show (l ^^^ 1) / 2 = v from litVar_litNeg l, hveq])
      subst hk_idx
      have hp : (l ^^^ 1) ^^^ 1 = l := litNeg_litNeg l
      exact Or.inl (by dsimp only [s', plainMinMarkState]; rwa [hkeq, hp])
    · have h2' : s.mrk[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#8 = 2#8 := by
        simpa [s', plainMinMarkState, List.getElem?_set_ne (Ne.symm hveq)] using h2
      exact plainMinMarkInv_lift_sound (s' := s') hcore ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
        hmono hmin.rem_sound hi' h2'

theorem plainMinMarkInv_mark_rem {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    {keep : List Nat} (hcore : PlainCoreInv c F0 s) (hmin : PlainMinMarkInv c F0 s keep)
    {idx0 : Nat} (hi0 : idx0 < s.trail_end)
    (hz : s.mrk[(s.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8)
    (hrsn : let p0 := (s.trl[idx0]?.getD 0#32).toNat
      let rsn := s.rsns[p0 / 2]?.getD 0xFFFFFFFF#32
      rsn ≠ 0xFFFFFFFF#32 ∧
      if (rsn &&& 0x80000000#32) ≠ 0#32 then
        let ot := (rsn &&& 0x7FFFFFFF#32).toNat
        ot < 2 * c.mv ∧ F0.EntailsClause (cnfClause [p0, ot]) ∧
        ∃ k < idx0, (s.trl[k]?.getD 0#32).toNat = ot ^^^ 1 ∧
          ((s.lvl[ot / 2]?.getD 0#32).toNat = 0 ∨ s.mrk[ot / 2]?.getD 0#8 = 2#8)
      else
        rsn.toNat ∈ arenaClauseRefs s ∧ arenaClauseGarb s rsn.toNat = false ∧
        ∀ q ∈ arenaClauseLits s rsn.toNat,
          q = p0 ∨ ∃ k < idx0, (s.trl[k]?.getD 0#32).toNat = q ^^^ 1 ∧
            ((s.lvl[q / 2]?.getD 0#32).toNat = 0 ∨ s.mrk[q / 2]?.getD 0#8 = 2#8)) :
    PlainMinMarkInv c F0
      (plainMinMarkState c s ((s.trl[idx0]?.getD 0#32).toNat / 2) 2#8) keep := by
  let v := (s.trl[idx0]?.getD 0#32).toNat / 2
  let s' := plainMinMarkState c s v 2#8; change PlainMinMarkInv c F0 s' keep
  have hlen := hcore.lengths
  have hv : v < c.mv := by have := hcore.trail_lits_lt idx0 hi0; omega
  have hmono : ∀ w < c.mv, s.mrk[w]?.getD 0#8 = 2#8 → s'.mrk[w]?.getD 0#8 = 2#8 := by
    intro w _ hw2
    by_cases hweq : w = v
    · subst w; rw [hz] at hw2; cases hw2
    · simp [s', plainMinMarkState, List.getElem?_set_ne (Ne.symm hweq), hw2]
  refine ⟨fun w hw => ?_, plain_clr_cov_mark_step hmin.clr_cov hv hlen.min_clr_len_arr 2#8,
    fun idx hi h2 => ?_⟩
  · by_cases hweq : w = v
    · subst w; right; left
      simp [s', plainMinMarkState, List.getElem?_set_self (by rw [hlen.mrk_len]; omega)]
    · simp only [s', plainMinMarkState, List.getElem?_set_ne (Ne.symm hweq)]
      exact hmin.mrk_dom w hw
  · have hi' : idx < s.trail_end := hi
    by_cases hveq : (s.trl[idx]?.getD 0#32).toNat / 2 = v
    · have hidx : idx = idx0 := hcore.trail_vars_nodup idx idx0 hi' hi0 hveq; subst hidx
      obtain ⟨hne, hif⟩ := hrsn; refine Or.inr ⟨hne, ?_⟩
      split at hif <;> split
      · obtain ⟨hot, hent, k, hk, hkeq, hdep⟩ := hif
        have hot_v : (s.rsns[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&&
            0x7FFFFFFF#32).toNat / 2 < c.mv := by omega
        exact ⟨hot, hent, k, hk, hkeq, hdep.elim Or.inl fun hk2 => Or.inr (hmono _ hot_v hk2)⟩
      · rename_i h1 h2; exact absurd h1 h2
      · rename_i h1 h2; exact absurd h2 h1
      · obtain ⟨href, hng, hall⟩ := hif; refine ⟨href, hng, fun q hq => ?_⟩
        rcases hall q hq with rfl | ⟨k, hk, hkeq, hdep⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨k, hk, hkeq, hdep.elim Or.inl fun hk2 =>
            Or.inr (hmono _ (plain_trail_xor_var_lt hcore (Nat.lt_trans hk hi0) hkeq) hk2)⟩
    · have h2' : s.mrk[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#8 = 2#8 := by
        simpa [s', plainMinMarkState, List.getElem?_set_ne (Ne.symm hveq)] using h2
      exact plainMinMarkInv_lift_sound (s' := s') hcore ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
        hmono hmin.rem_sound hi' h2'

theorem plainMinMarkInv_drop {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    {keep keep' : List Nat} (hcore : PlainCoreInv c F0 s) (hmin : PlainMinMarkInv c F0 s keep)
    {root_lit : Nat} (hsub : ∀ l ∈ keep, l = root_lit ∨ l ∈ keep')
    {idx0 : Nat} (hi0 : idx0 < s.trail_end)
    (hroot : (s.trl[idx0]?.getD 0#32).toNat = root_lit ^^^ 1)
    (hrsn : let p0 := root_lit ^^^ 1
      let rsn := s.rsns[p0 / 2]?.getD 0xFFFFFFFF#32
      rsn ≠ 0xFFFFFFFF#32 ∧
      if (rsn &&& 0x80000000#32) ≠ 0#32 then
        let ot := (rsn &&& 0x7FFFFFFF#32).toNat
        ot < 2 * c.mv ∧ F0.EntailsClause (cnfClause [p0, ot]) ∧
        ∃ k < idx0, (s.trl[k]?.getD 0#32).toNat = ot ^^^ 1 ∧
          ((s.lvl[ot / 2]?.getD 0#32).toNat = 0 ∨ s.mrk[ot / 2]?.getD 0#8 = 2#8)
      else
        rsn.toNat ∈ arenaClauseRefs s ∧ arenaClauseGarb s rsn.toNat = false ∧
        ∀ q ∈ arenaClauseLits s rsn.toNat,
          q = p0 ∨ ∃ k < idx0, (s.trl[k]?.getD 0#32).toNat = q ^^^ 1 ∧
            ((s.lvl[q / 2]?.getD 0#32).toNat = 0 ∨ s.mrk[q / 2]?.getD 0#8 = 2#8)) :
    PlainMinMarkInv c F0 s keep' := by
  refine ⟨hmin.mrk_dom, hmin.clr_cov, fun idx hi h2 => ?_⟩
  rcases hmin.rem_sound idx hi h2 with hin | hok
  · rcases hsub _ hin with heq | hin'
    · have hv_eq : (s.trl[idx]?.getD 0#32).toNat / 2 = (s.trl[idx0]?.getD 0#32).toNat / 2 := by
        rw [hroot]
        have h1 : ((s.trl[idx]?.getD 0#32).toNat ^^^ 1) / 2 =
            (s.trl[idx]?.getD 0#32).toNat / 2 := litVar_litNeg _
        have h2' : (root_lit ^^^ 1) / 2 = root_lit / 2 := litVar_litNeg root_lit
        rw [← h1, heq, h2']
      have hidx : idx = idx0 := hcore.trail_vars_nodup idx idx0 hi hi0 hv_eq
      subst hidx; rw [hroot]; exact Or.inr hrsn
    · exact Or.inl hin'
  · exact Or.inr hok

private theorem plain_trail_lit_false_strong {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    {keep : List Nat} (hcore : PlainCoreInv c F0 s) (hmin : PlainMinMarkInv c F0 s keep)
    (α : Nat → Bool) (hα : F0.Sat α)
    (hkeep_false : ∀ l ∈ keep, α (litVar l) ≠ !(litSign l)) :
    ∀ i < s.trail_end, let p := (s.trl[i]?.getD 0#32).toNat
      (s.lvl[p / 2]?.getD 0#32).toNat = 0 ∨ s.mrk[p / 2]?.getD 0#8 = 2#8 →
      α (litVar p) = !(litSign p) := by
  intro i hi p hcond
  rcases hcond with hl0 | hrem
  · exact (sat_cnfClause_singleton α p).mp
      (CNF.entails_clause_def.mp (hcore.level0_sound i hi hl0) α hα)
  · rcases hmin.rem_sound i hi hrem with hin | ⟨_, hif⟩
    · have hf := hkeep_false _ hin
      have hv : litVar (p ^^^ 1) = litVar p := litVar_litNeg p
      have hs : litSign (p ^^^ 1) = !(litSign p) := litSign_litNeg p
      rw [hv, hs] at hf; cases h1 : α (litVar p) <;> cases h2 : litSign p <;> simp_all
    · have hcontra : ∀ (q k : Nat), k < i → (s.trl[k]?.getD 0#32).toNat = q ^^^ 1 →
          ((s.lvl[q / 2]?.getD 0#32).toNat = 0 ∨ s.mrk[q / 2]?.getD 0#8 = 2#8) →
          α (litVar q) = !(litSign q) → False := fun q k hk hkeq hkcond hqsat => by
        have hkq : (s.trl[k]?.getD 0#32).toNat / 2 = q / 2 := by rw [hkeq]; exact litVar_litNeg q
        have hkf := plain_trail_lit_false_strong hcore hmin α hα hkeep_false k
          (Nat.lt_trans hk hi) (by rw [hkq]; exact hkcond)
        have hv : litVar (q ^^^ 1) = litVar q := litVar_litNeg q
        have hs : litSign (q ^^^ 1) = !(litSign q) := litSign_litNeg q
        rw [hkeq, hv, hs] at hkf; cases h1 : α (litVar q) <;> cases h2 : litSign q <;> simp_all
      split at hif
      · obtain ⟨_, hent, k, hk, hkeq, hkcond⟩ := hif
        obtain ⟨q, hq, hqsat⟩ := (clause_sat_cnfClause_iff α _).mp
          (CNF.entails_clause_def.mp hent α hα)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | hq
        · exact hqsat
        · exact False.elim (hcontra _ k hk hkeq hkcond (hq ▸ hqsat))
      · obtain ⟨href, hng, hall⟩ := hif
        obtain ⟨q, hq, hqsat⟩ := (clause_sat_cnfClause_iff α _).mp
          (CNF.entails_clause_def.mp (hcore.arena.entails _ href hng) α hα)
        rcases hall q hq with rfl | ⟨k, hk, hkeq, hkcond⟩
        · exact hqsat
        · exact False.elim (hcontra q k hk hkeq hkcond hqsat)
termination_by i => i

/-- Soundness of clause minimization via `PlainMinMarkInv`: if every literal of `orig` is
falsified and either kept in `keep` or marked `REMOVABLE` (`2#8`), then `F0` entails `keep`. -/
theorem plainMinMark_entails {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    {orig keep : List Nat} (hcore : PlainCoreInv c F0 s) (hmin : PlainMinMarkInv c F0 s keep)
    (horig : F0.EntailsClause (cnfClause orig))
    (hspec : ∀ l ∈ orig, l < 2 * c.mv ∧ s.vals[l]?.getD 0#8 = 0xFF#8 ∧
      (l ∈ keep ∨ s.mrk[l / 2]?.getD 0#8 = 2#8)) :
    F0.EntailsClause (cnfClause keep) := by
  rw [CNF.entails_clause_def] at horig ⊢; intro α hα
  by_cases hsat : (keep.any fun l => α (litVar l) == !(litSign l)) = true
  · obtain ⟨l, hl, hlt⟩ := List.any_eq_true.mp hsat
    exact (clause_sat_cnfClause_iff α keep).mpr ⟨l, hl, beq_iff_eq.mp hlt⟩
  · exfalso
    have hkf : ∀ l ∈ keep, α (litVar l) ≠ !(litSign l) := fun l hl heq =>
      hsat (List.any_eq_true.mpr ⟨l, hl, beq_iff_eq.mpr heq⟩)
    obtain ⟨l, hl, hlsat⟩ := (clause_sat_cnfClause_iff α orig).mp (horig α hα)
    obtain ⟨hlt, hfals, hkm⟩ := hspec l hl
    rcases hkm with hin | hmrk
    · exact hkf l hin hlsat
    · obtain ⟨i, hi, hieq⟩ := (hcore.vals_false_iff l hlt).mp hfals
      have hvar : (s.trl[i]?.getD 0#32).toNat / 2 = l / 2 := by rw [hieq]; exact litVar_litNeg l
      have htf := plain_trail_lit_false_strong hcore hmin α hα hkf i hi
        (Or.inr (by rw [hvar]; exact hmrk))
      have hv : litVar (l ^^^ 1) = litVar l := litVar_litNeg l
      have hs : litSign (l ^^^ 1) = !(litSign l) := litSign_litNeg l
      rw [hieq, hv, hs, hlsat] at htf; cases hls : litSign l <;> simp_all

end LeanQbe.T.Examples.Kissat.Plain
