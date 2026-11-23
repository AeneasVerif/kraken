module

public import LeanQbe.T.Examples.Kissat.SolverSpec
import all Kraken.Mem
import all Kraken.Separation

/-!
# Soundness Proofs for Kissat `D-Min` C0 State Init & Syntax Skip (Part 1)

Proves `Func.wp` specifications for the 4 initialization and clause-ingestion functions in
`LeanQbe.T.Examples.Kissat.Solver`:
1. `kissat_init_state` (`kissatInitStateSpec`, `kissat_init_state_wp`)
2. `kissat_skip_clause_syntax` (`kissatSkipClauseSyntaxSpec`, `kissat_skip_clause_syntax_wp`)
3. `kissat_ingest_clause` (`kissatIngestClauseSpec`, `kissat_ingest_clause_wp`)
4. `kissat_parse_body` (`kissatParseBodySpec`, `kissat_parse_body_wp`)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open Kraken.Bedrock2.Test

/-! ## 1. Pure arithmetic, region splitting, parser, and invariant helpers -/

private theorem bv64_align8 {n : Nat} (hn : n + 7 < 2 ^ 64) :
    (BitVec.ofNat 64 n + (7 : BitVec 64)) &&& (~~~(7 : BitVec 64)) =
      BitVec.ofNat 64 (((n + 7) / 8) * 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [show (7 : BitVec 64) = BitVec.ofNat 64 7 from rfl, bv_add_ofNat]
  have h1 : BitVec.ofNat 64 (n + 7) &&& ~~~(BitVec.ofNat 64 7) =
      BitVec.ofNat 64 (((n + 7) / 8) * 8) := by
    apply BitVec.eq_of_toNat_eq
    have hmod : (n + 7) % 2 ^ 64 = n + 7 := Nat.mod_eq_of_lt hn
    have hmod2 : (((n + 7) / 8) * 8) % 2 ^ 64 = ((n + 7) / 8) * 8 :=
      Nat.mod_eq_of_lt (by omega)
    simp only [BitVec.toNat_and, BitVec.toNat_not, BitVec.toNat_ofNat, hmod, hmod2]
    have hnot : (2 ^ 64 - 1 - 7 % 2 ^ 64) = 2 ^ 64 - 8 := by decide
    rw [hnot]
    have hdiv := Nat.and_div_two_pow (a := n + 7) (b := 2 ^ 64 - 8) (n := 3)
    have hrem := Nat.and_mod_two_pow (a := n + 7) (b := 2 ^ 64 - 8) (n := 3)
    have hbdiv : (2 ^ 64 - 8) / 2 ^ 3 = 2 ^ 61 - 1 := by decide
    have hbrem : (2 ^ 64 - 8) % 2 ^ 3 = 0 := by decide
    rw [hbdiv] at hdiv; rw [hbrem, Nat.and_zero] at hrem
    have hq : ((n + 7) / 8) &&& (2 ^ 61 - 1) = (n + 7) / 8 := by
      have hlt : (n + 7) / 8 < 2 ^ 61 := by omega
      simpa [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hlt] using
        Nat.and_two_pow_sub_one_eq_mod ((n + 7) / 8) 61
    have hpow : (2 ^ 3 : Nat) = 8 := by decide
    rw [hpow] at hdiv hrem
    rw [hq] at hdiv
    omega
  exact congrArg BitVec.toNat h1

private theorem bv64_mul24 (n : Nat) :
    BitVec.ofNat 64 n * (24 : BitVec 64) = BitVec.ofNat 64 (n * 24) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, Nat.mul_mod]

theorem bv32_and1_add1 (x : BitVec 32) :
    ((x &&& (1 : BitVec 32)) + (1 : BitVec 32)).setWidth 8 =
      BitVec.ofNat 8 (x.toNat % 2 + 1) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (x &&& (1 : BitVec 32)).toNat = x.toNat % 2 := bv32_and_1 x
  have h2 : (1 : BitVec 32).toNat = 1 := rfl
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, h1, h2, BitVec.toNat_ofNat]
  omega

theorem bv8_zext32_eq {a b : BitVec 8} :
    a.setWidth 32 = b.setWidth 32 ↔ a = b := by
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    have ht := congrArg BitVec.toNat h
    have ha : a.toNat < 2 ^ 32 := by have := a.isLt; omega
    have hb : b.toNat < 2 ^ 32 := by have := b.isLt; omega
    simp only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at ht
    exact ht
  · intro h; rw [h]

/-- Pure `max_c` computed by `kissat_init_state`. -/
def initMaxC (nc rem : Nat) : Nat :=
  min (nc + (rem - nc * 24) / 64) (dimacsBound - 1)

/-- Pure `lcap` computed by `kissat_init_state`. -/
def initLcap (nc rem : Nat) : Nat :=
  min ((rem - initMaxC nc rem * 24) / 4) (dimacsBound - 1)

theorem initMaxC_lt {nc rem : Nat} : initMaxC nc rem < dimacsBound := by
  unfold initMaxC dimacsBound; omega

theorem initLcap_lt {nc rem : Nat} : initLcap nc rem < dimacsBound := by
  unfold initLcap dimacsBound; omega

theorem initMaxC_mul24_le {nc rem : Nat} (h : nc * 24 ≤ rem) :
    initMaxC nc rem * 24 ≤ rem := by
  unfold initMaxC; omega

theorem init_arena_fits {mv nc avail : Nat} (h : fixedBytes mv + nc * 24 ≤ avail) :
    let rem := avail - fixedBytes mv
    fixedBytes mv + 24 * initMaxC nc rem + 4 * initLcap nc rem ≤ avail := by
  intro rem
  have h1 : initMaxC nc rem * 24 ≤ rem := initMaxC_mul24_le (by omega)
  have h2 : 4 * initLcap nc rem ≤ rem - initMaxC nc rem * 24 := by
    unfold initLcap; omega
  omega

/-- Split `region (c.hdr + 200) (c.avail - 200)` into the 10 uninitialized arrays + `c.pad`. -/
theorem ArenaCfg.avail_to_arrays (c : ArenaCfg) {m : Mem 64}
    (hm : region (c.hdr + BitVec.ofNat 64 200) (c.avail - 200) m) :
    ∃ (vals mrk : List (BitVec 8)) (lvl rsns trl tmp wh cls wn lpool : List (BitVec 32)),
      vals.length = 2 * c.mv ∧ mrk.length = c.mv ∧ lvl.length = c.mv ∧ rsns.length = c.mv ∧
      trl.length = c.mv ∧ tmp.length = c.mv ∧ wh.length = 2 * c.mv ∧
      cls.length = 4 * c.max_c ∧ wn.length = 2 * c.max_c ∧ lpool.length = c.lcap ∧
      (array (t := i8) c.pVals vals ⋆
        array (t := i8) c.pMark mrk ⋆
        array (t := i32) c.pLevel lvl ⋆
        array (t := i32) c.pReason rsns ⋆
        array (t := i32) c.pTrail trl ⋆
        array (t := i32) c.pTmp tmp ⋆
        array (t := i32) c.pWh wh ⋆
        array (t := i32) c.pClauses cls ⋆
        array (t := i32) c.pWn wn ⋆
        array (t := i32) c.pLpool lpool ⋆
        c.pad) m := by
  have hmv := c.hmv; have hmc := c.hmax_c; have hlc := c.hlcap
  unfold dimacsBound at hmv hmc hlc
  have hfit := c.havail_fit; have hsz := c.hsize
  have hv := valsBytes_ge c.mv; have hmk := markBytes_ge c.mv
  have hu := u32VarBytes_ge c.mv; have hw := whBytes_ge c.mv
  have hfx := fixedBytes_lt c.hmv
  unfold fixedBytes at hsz hfx
  have h0 : region c.pVals (c.avail - 200) m := hm
  rw [← region_merge_eq (a := c.pVals) (n1 := valsBytes c.mv)
      (n2 := c.avail - 200 - valsBytes c.mv) (n := c.avail - 200) (by omega) (by omega)] at h0
  rw [← show c.pMark = c.pVals + BitVec.ofNat 64 (valsBytes c.mv) from rfl] at h0
  rw [← region_merge_eq (a := c.pMark) (n1 := markBytes c.mv)
      (n2 := c.avail - 200 - valsBytes c.mv - markBytes c.mv)
      (n := c.avail - 200 - valsBytes c.mv) (by omega) (by omega)] at h0
  rw [← show c.pLevel = c.pMark + BitVec.ofNat 64 (markBytes c.mv) from rfl] at h0
  rw [← region_merge_eq (a := c.pLevel) (n1 := u32VarBytes c.mv)
      (n2 := c.avail - 200 - valsBytes c.mv - markBytes c.mv - u32VarBytes c.mv)
      (n := c.avail - 200 - valsBytes c.mv - markBytes c.mv) (by omega) (by omega)] at h0
  rw [← show c.pReason = c.pLevel + BitVec.ofNat 64 (u32VarBytes c.mv) from rfl] at h0
  rw [← region_merge_eq (a := c.pReason) (n1 := u32VarBytes c.mv)
      (n2 := c.avail - 200 - valsBytes c.mv - markBytes c.mv - 2 * u32VarBytes c.mv)
      (n := c.avail - 200 - valsBytes c.mv - markBytes c.mv - u32VarBytes c.mv)
      (by omega) (by omega)] at h0
  rw [← show c.pTrail = c.pReason + BitVec.ofNat 64 (u32VarBytes c.mv) from rfl] at h0
  rw [← region_merge_eq (a := c.pTrail) (n1 := u32VarBytes c.mv)
      (n2 := c.avail - 200 - valsBytes c.mv - markBytes c.mv - 3 * u32VarBytes c.mv)
      (n := c.avail - 200 - valsBytes c.mv - markBytes c.mv - 2 * u32VarBytes c.mv)
      (by omega) (by omega)] at h0
  rw [← show c.pTmp = c.pTrail + BitVec.ofNat 64 (u32VarBytes c.mv) from rfl] at h0
  rw [← region_merge_eq (a := c.pTmp) (n1 := u32VarBytes c.mv)
      (n2 := c.avail - 200 - valsBytes c.mv - markBytes c.mv - 4 * u32VarBytes c.mv)
      (n := c.avail - 200 - valsBytes c.mv - markBytes c.mv - 3 * u32VarBytes c.mv)
      (by omega) (by omega)] at h0
  rw [← show c.pWh = c.pTmp + BitVec.ofNat 64 (u32VarBytes c.mv) from rfl] at h0
  rw [← region_merge_eq (a := c.pWh) (n1 := whBytes c.mv)
      (n2 := c.avail - fixedBytes c.mv)
      (n := c.avail - 200 - valsBytes c.mv - markBytes c.mv - 4 * u32VarBytes c.mv)
      (by unfold fixedBytes; omega) (by omega)] at h0
  rw [← show c.pClauses = c.pWh + BitVec.ofNat 64 (whBytes c.mv) from rfl] at h0
  rw [← region_merge_eq (a := c.pClauses) (n1 := 24 * c.max_c)
      (n2 := c.avail - fixedBytes c.mv - 24 * c.max_c) (n := c.avail - fixedBytes c.mv)
      (by unfold fixedBytes; omega) (by omega)] at h0
  rw [← show c.pLpool = c.pClauses + BitVec.ofNat 64 (24 * c.max_c) from rfl] at h0
  rw [← region_merge_eq (a := c.pLpool) (n1 := 4 * c.lcap) (n2 := c.slack)
      (n := c.avail - fixedBytes c.mv - 24 * c.max_c)
      (by unfold ArenaCfg.slack fixedBytes; omega) (by omega)] at h0
  rw [← show c.pSlack = c.pLpool + BitVec.ofNat 64 (4 * c.lcap) from rfl] at h0
  rw [← region_merge_eq (a := c.pClauses) (n1 := 16 * c.max_c) (n2 := 8 * c.max_c)
      (n := 24 * c.max_c) (by omega) (by omega)] at h0
  rw [← show c.pWn = c.pClauses + BitVec.ofNat 64 (16 * c.max_c) from rfl] at h0
  rw [← region_merge_eq (a := c.pVals) (n1 := 2 * c.mv) (n2 := valsBytes c.mv - 2 * c.mv)
      (n := valsBytes c.mv) (by omega) (by omega),
    ← region_merge_eq (a := c.pMark) (n1 := c.mv) (n2 := markBytes c.mv - c.mv)
      (n := markBytes c.mv) (by omega) (by omega),
    ← region_merge_eq (a := c.pLevel) (n1 := 4 * c.mv) (n2 := u32VarBytes c.mv - 4 * c.mv)
      (n := u32VarBytes c.mv) (by omega) (by omega),
    ← region_merge_eq (a := c.pReason) (n1 := 4 * c.mv) (n2 := u32VarBytes c.mv - 4 * c.mv)
      (n := u32VarBytes c.mv) (by omega) (by omega),
    ← region_merge_eq (a := c.pTrail) (n1 := 4 * c.mv) (n2 := u32VarBytes c.mv - 4 * c.mv)
      (n := u32VarBytes c.mv) (by omega) (by omega),
    ← region_merge_eq (a := c.pTmp) (n1 := 4 * c.mv) (n2 := u32VarBytes c.mv - 4 * c.mv)
      (n := u32VarBytes c.mv) (by omega) (by omega),
    ← region_merge_eq (a := c.pWh) (n1 := 8 * c.mv) (n2 := whBytes c.mv - 8 * c.mv)
      (n := whBytes c.mv) (by omega) (by omega)] at h0
  have h1 : (region c.pVals (2 * c.mv) ⋆
      (region c.pMark c.mv ⋆
      (region c.pLevel (4 * c.mv) ⋆
      (region c.pReason (4 * c.mv) ⋆
      (region c.pTrail (4 * c.mv) ⋆
      (region c.pTmp (4 * c.mv) ⋆
      (region c.pWh (8 * c.mv) ⋆
      (region c.pClauses (16 * c.max_c) ⋆
      (region c.pWn (8 * c.max_c) ⋆
      (region c.pLpool (4 * c.lcap) ⋆
      c.pad)))))))))) m := by
    unfold ArenaCfg.pad; exact sep_ac h0
  rcases h1 with ⟨m1, m_r1, hu1, hd1, h_vals, h_r1⟩
  rcases h_r1 with ⟨m2, m_r2, hu2, hd2, h_mrk, h_r2⟩
  rcases h_r2 with ⟨m3, m_r3, hu3, hd3, h_lvl, h_r3⟩
  rcases h_r3 with ⟨m4, m_r4, hu4, hd4, h_rsn, h_r4⟩
  rcases h_r4 with ⟨m5, m_r5, hu5, hd5, h_trl, h_r5⟩
  rcases h_r5 with ⟨m6, m_r6, hu6, hd6, h_tmp, h_r6⟩
  rcases h_r6 with ⟨m7, m_r7, hu7, hd7, h_wh, h_r7⟩
  rcases h_r7 with ⟨m8, m_r8, hu8, hd8, h_cls, h_r8⟩
  rcases h_r8 with ⟨m9, m_r9, hu9, hd9, h_wn, h_r9⟩
  rcases h_r9 with ⟨m10, m_pad, hu10, hd10, h_lp, h_pad⟩
  obtain ⟨vals, hvl, h_vals'⟩ := region_to_array_i8 (2 * c.mv) (by omega) h_vals
  obtain ⟨mrk, hmkl, h_mrk'⟩ := region_to_array_i8 c.mv (by omega) h_mrk
  obtain ⟨lvl, hll, h_lvl'⟩ := region_to_array_i32 c.mv (by omega) h_lvl
  obtain ⟨rsns, hrsl, h_rsn'⟩ := region_to_array_i32 c.mv (by omega) h_rsn
  obtain ⟨trl, htrl, h_trl'⟩ := region_to_array_i32 c.mv (by omega) h_trl
  obtain ⟨tmp, htmpl, h_tmp'⟩ := region_to_array_i32 c.mv (by omega) h_tmp
  obtain ⟨wh, hwhl, h_wh'⟩ := region_to_array_i32 (2 * c.mv) (by omega) (by
    simpa [show 4 * (2 * c.mv) = 8 * c.mv by omega] using h_wh)
  obtain ⟨cls, hclsl, h_cls'⟩ := region_to_array_i32 (4 * c.max_c) (by omega) (by
    simpa [show 4 * (4 * c.max_c) = 16 * c.max_c by omega] using h_cls)
  obtain ⟨wn, hwnl, h_wn'⟩ := region_to_array_i32 (2 * c.max_c) (by omega) (by
    simpa [show 4 * (2 * c.max_c) = 8 * c.max_c by omega] using h_wn)
  obtain ⟨lpool, hlpl, h_lp'⟩ := region_to_array_i32 c.lcap (by omega) h_lp
  have h_res : (array (t := i8) c.pVals vals ⋆
      (array (t := i8) c.pMark mrk ⋆
      (array (t := i32) c.pLevel lvl ⋆
      (array (t := i32) c.pReason rsns ⋆
      (array (t := i32) c.pTrail trl ⋆
      (array (t := i32) c.pTmp tmp ⋆
      (array (t := i32) c.pWh wh ⋆
      (array (t := i32) c.pClauses cls ⋆
      (array (t := i32) c.pWn wn ⋆
      (array (t := i32) c.pLpool lpool ⋆ c.pad)))))))))) m :=
    ⟨m1, m_r1, hu1, hd1, h_vals', m2, m_r2, hu2, hd2, h_mrk', m3, m_r3, hu3, hd3, h_lvl',
      m4, m_r4, hu4, hd4, h_rsn', m5, m_r5, hu5, hd5, h_trl', m6, m_r6, hu6, hd6, h_tmp',
      m7, m_r7, hu7, hd7, h_wh', m8, m_r8, hu8, hd8, h_cls', m9, m_r9, hu9, hd9, h_wn',
      m10, m_pad, hu10, hd10, h_lp', h_pad⟩
  exact ⟨vals, mrk, lvl, rsns, trl, tmp, wh, cls, wn, lpool,
    hvl, hmkl, hll, hrsl, htrl, htmpl, hwhl, hclsl, hwnl, hlpl, sep_ac h_res⟩

/-- Every variable in a clause returned by `parseClauseAux` is positive when `acc` is positive. -/
theorem parseClauseAux_vars_pos {fuel mv : Nat} {acc : List (Literal Nat)}
    {bs rest : List UInt8} {cl : CNF.Clause Nat}
    (hacc : ∀ lit ∈ acc, 1 ≤ lit.1)
    (h : parseClauseAux fuel mv acc bs = some (cl, rest)) :
    ∀ lit ∈ cl.literals, 1 ≤ lit.1 := by
  induction fuel generalizing acc bs with
  | zero => simp [parseClauseAux] at h
  | succ fuel ih =>
    rw [parseClauseAux_eq_nextLitPure] at h
    cases hn : nextLitPure mv bs with
    | err => rw [hn] at h; cases h
    | endClause rest' =>
      rw [hn] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      intro lit hlit
      simp only [CNF.Clause.literals_ofLiterals, List.mem_reverse] at hlit
      exact hacc lit hlit
    | lit l rest' =>
      rw [hn] at h
      refine ih (fun lit hlit => ?_) h
      rcases List.mem_cons.mp hlit with rfl | hm
      · simp [kissatLitToDimacsLiteral]
      · exact hacc lit hm

theorem kissatLitToDimacsLiteral_inj {l1 l2 : Nat}
    (h : kissatLitToDimacsLiteral l1 = kissatLitToDimacsLiteral l2) : l1 = l2 := by
  unfold kissatLitToDimacsLiteral litVar litSign at h
  simp only [Prod.mk.injEq, Bool.not_inj_iff] at h
  rcases h with ⟨hv, hs⟩
  rcases Nat.mod_two_eq_zero_or_one l1 with h1 | h1 <;>
    rcases Nat.mod_two_eq_zero_or_one l2 with h2 | h2 <;> simp [h1, h2] at hs <;> omega

/-- Initial zeroed state produced by `kissat_init_state` satisfies `SolverInv`. -/
theorem solverInv_init {c : ArenaCfg} {s : ArenaState}
    (hlen : s.LengthsOk c)
    (_hll : s.lit_len = 0) (hnc : s.num_clauses = 0) (hte : s.trail_end = 0)
    (_hpr : s.propagated = 0) (hcl : s.cur_level = 0)
    (hvals : s.vals = List.replicate (2 * c.mv) 0#8)
    (hmrk : s.mrk = List.replicate c.mv 0#8) :
    SolverInv c (shiftDownCnf CNF.empty) s := by
  refine ⟨⟨hlen,
    ⟨fun _ h => by omega, fun _ _ _ h => by omega, fun _ h => by omega, fun _ h => by omega⟩,
    by omega, fun _ h => by omega, fun _ _ h => by omega,
    fun l hl => by rw [hvals]; simp [hl],
    fun l hl => by rw [hvals, hte]; simp [hl],
    fun l hl => by rw [hvals, hte]; simp [hl],
    fun _ h => by omega, fun _ _ _ h => by omega, fun _ h1 h2 => by omega,
    fun _ h => by omega, fun _ h => by omega⟩,
    fun v hv => by rw [hmrk]; simp [hv]⟩

/-- Deterministic unit-only SAT trace (all clauses are unit-assigning and non-conflicting). -/
inductive UnitSatTrace (mv : Nat) : List (BitVec 8) → Nat → List UInt8 → Nat →
    List (BitVec 8) → Nat → Prop where
  | done {vals te bs} :
      (skipWsComments bs).isEmpty = true →
      UnitSatTrace mv vals te bs 0 vals te
  | step {vals te bs l rest k vals' te'} :
      l < 2 * mv →
      parseClause mv bs = some (CNF.Clause.ofLiterals [kissatLitToDimacsLiteral l], rest) →
      vals[l]?.getD 0#8 = 0#8 →
      UnitSatTrace mv ((vals.set l 1#8).set (l ^^^ 1) 0xFF#8) (te + 1) rest k vals' te' →
      UnitSatTrace mv vals te bs (k + 1) vals' te'

/-- Deterministic unit-only UNSAT trace (unit prefix ending in a unit conflict, valid tail). -/
inductive UnitUnsatTrace (mv : Nat) : List (BitVec 8) → List UInt8 → Nat → Prop where
  | conflict {vals bs l rest k} :
      l < 2 * mv →
      parseClause mv bs = some (CNF.Clause.ofLiterals [kissatLitToDimacsLiteral l], rest) →
      vals[l]?.getD 0#8 = 0xFF#8 →
      (∃ cnf, parseClauses mv k CNF.empty rest = some cnf) →
      UnitUnsatTrace mv vals bs (k + 1)
  | step {vals bs l rest k} :
      l < 2 * mv →
      parseClause mv bs = some (CNF.Clause.ofLiterals [kissatLitToDimacsLiteral l], rest) →
      vals[l]?.getD 0#8 = 0#8 →
      UnitUnsatTrace mv ((vals.set l 1#8).set (l ^^^ 1) 0xFF#8) rest k →
      UnitUnsatTrace mv vals bs (k + 1)

theorem parseClauses_some_of_acc {mv k : Nat} {bs : List UInt8}
    {acc1 acc2 cnf1 : CNF Nat}
    (h : parseClauses mv k acc1 bs = some cnf1) :
    ∃ cnf2, parseClauses mv k acc2 bs = some cnf2 := by
  induction k generalizing bs acc1 acc2 with
  | zero =>
    simp only [parseClauses] at h ⊢
    split at h
    · exact ⟨acc2, by simp_all⟩
    · cases h
  | succ k ih =>
    simp only [parseClauses] at h ⊢
    cases hpc : parseClause mv bs with
    | none => rw [hpc] at h; cases h
    | some p =>
      rcases p with ⟨cl, rest⟩
      rw [hpc] at h
      exact ih h

theorem cnf_unsat_add {F : CNF Nat} {cl : CNF.Clause Nat}
    (hu : F.Unsat) : (F.add cl).Unsat := by
  rw [CNF.unsat_iff_not_sat] at hu ⊢
  intro α hα; exact hu α (CNF.sat_add.mp hα).2

/-! ## 2. `kissat_init_state` specification and `Func.wp` proof -/

/-- Specification of `kissat_init_state(cnf_ptr, cnf_end, hdr_addr, avail, fuel)`. -/
def kissatInitStateSpec : Spec [i64, i64, i64, i64, i64] [.bool] :=
  fun (cnf_ptr, cend, hdr_addr, avail, fuel, ()) m Q _ =>
    ∃ (cnfBytes : List UInt8) (R : Mem 64 → Prop),
      cend = cnf_ptr + BitVec.ofNat 64 cnfBytes.length ∧
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
      hdr_addr.toNat + avail.toNat < 2 ^ 64 ∧
      200 ≤ avail.toNat ∧
      (bytes cnf_ptr cnfBytes ⋆ region hdr_addr avail.toNat ⋆ R) m ∧
      (∀ m', (bytes cnf_ptr cnfBytes ⋆ region hdr_addr avail.toNat ⋆ R) m' →
        (∀ mv nc rest, parseHeader cnfBytes = some (mv, nc, rest) →
          avail.toNat < fixedBytes mv + nc * 24) →
        Q (false, ()) m') ∧
      (∀ (c : ArenaCfg) (s : ArenaState) (j : Nat) (rest : List UInt8) (m' : Mem 64),
        c.hdr = hdr_addr → c.avail = avail.toNat →
        parseHeader cnfBytes = some (c.mv, c.nc, rest) →
        j ≤ cnfBytes.length → cnfBytes.drop j = rest →
        SolverInv c (shiftDownCnf CNF.empty) s →
        s.d_cur = cnf_ptr + BitVec.ofNat 64 j →
        s.lit_len = 0 → s.num_clauses = 0 → s.trail_end = 0 → s.propagated = 0 →
        s.cur_level = 0 → s.fuel = fuel →
        s.vals = List.replicate (2 * c.mv) 0#8 →
        s.wh = List.replicate (2 * c.mv) 0xFFFFFFFF#32 →
        (bytes cnf_ptr cnfBytes ⋆ ArenaMem c s ⋆ R) m' →
        Q (true, ()) m')

theorem kissat_init_state_wp (Γ : Env)
    (hHdr : ∀ args m Q X, kissatParseHeaderSpec args m Q X →
      Γ "kissat_parse_header" [i64, i64, i64] [.bool] args m Q X)
    (hZero : ∀ args m Q X, kissatZeroTablesSpec args m Q X →
      Γ "kissat_zero_tables" [i64] [] args m Q X) :
    ∀ args m Q X, kissatInitStateSpec args m Q X →
      Func.wp Γ kissat_init_state_body args m Q X := by
  rintro ⟨cnf_ptr, cend, hdr_addr, avail, fuel, ⟨⟩⟩ m Q X
    ⟨cnfBytes, R, rfl, hfit, havel_fit, hav200, hm, hQfalse, hQtrue⟩
  unfold Func.wp kissat_init_state_body; wp_unfold
  have hav_le : avail.toNat ≤ 2 ^ 64 := by omega
  have hsplit1 : (bytes cnf_ptr cnfBytes ⋆
      (region hdr_addr 32 ⋆ region (hdr_addr + BitVec.ofNat 64 32) (avail.toNat - 32)) ⋆ R) m := by
    rwa [region_merge_eq (a := hdr_addr) (n1 := 32) (n2 := avail.toNat - 32)
      (n := avail.toNat) (by omega) hav_le]
  have hsplit1' : ((region hdr_addr 32) ⋆
      (bytes cnf_ptr cnfBytes ⋆ region (hdr_addr + BitVec.ofNat 64 32) (avail.toNat - 32) ⋆ R)) m :=
    sep_ac hsplit1
  rcases hsplit1' with ⟨m_d, m_o, hu_do, hd_do, h_d32, h_o⟩
  obtain ⟨mv0, nc0, cur0, val0, h_dstate⟩ := region32_to_dimacsState h_d32
  have hm_pre0 : (dimacsState hdr_addr mv0 nc0 cur0 val0 ⋆
      (bytes cnf_ptr cnfBytes ⋆
        region (hdr_addr + BitVec.ofNat 64 32) (avail.toNat - 32) ⋆ R)) m :=
    ⟨m_d, m_o, hu_do, hd_do, h_dstate, h_o⟩
  have hm_pre : (bytes cnf_ptr cnfBytes ⋆ dimacsState hdr_addr mv0 nc0 cur0 val0 ⋆
      (region (hdr_addr + BitVec.ofNat 64 32) (avail.toNat - 32) ⋆ R)) m :=
    sep_ac hm_pre0
  have hremerge : ∀ mv' nc' cur' val' m',
      (bytes cnf_ptr cnfBytes ⋆ dimacsState hdr_addr mv' nc' cur' val' ⋆
        (region (hdr_addr + BitVec.ofNat 64 32) (avail.toNat - 32) ⋆ R)) m' →
      (bytes cnf_ptr cnfBytes ⋆ region hdr_addr avail.toNat ⋆ R) m' := by
    intro mv' nc' cur' val' m' hm'
    have h1 : ((dimacsState hdr_addr mv' nc' cur' val' ⋆
        region (hdr_addr + BitVec.ofNat 64 32) (avail.toNat - 32)) ⋆
        (bytes cnf_ptr cnfBytes ⋆ R)) m' := sep_ac hm'
    have h2 : ((region hdr_addr 32 ⋆
        region (hdr_addr + BitVec.ofNat 64 32) (avail.toNat - 32)) ⋆
        (bytes cnf_ptr cnfBytes ⋆ R)) m' :=
      sep_mono2 (sep_mono2 (fun _ h => dimacsState_to_region h) (fun _ h => h))
        (fun _ h => h) m' h1
    rw [region_merge_eq (a := hdr_addr) (n1 := 32) (n2 := avail.toNat - 32)
      (n := avail.toNat) (by omega) hav_le] at h2
    exact sep_ac h2
  apply wp_call_of_spec; apply hHdr
  change kissatParseHeaderSpec
    (cnf_ptr, cnf_ptr + BitVec.ofNat 64 cnfBytes.length, hdr_addr, ()) m _ _
  refine ⟨mv0, nc0, cur0, val0, cnfBytes,
    region (hdr_addr + BitVec.ofNat 64 32) (avail.toNat - 32) ⋆ R, rfl, hfit, hm_pre, ?_⟩
  cases hhdr : parseHeader cnfBytes with
  | none =>
    intro mv' nc' cur' val' m' hm'
    wp_unfold
    exact hQfalse m' (hremerge _ _ _ _ m' hm') (fun _ _ _ h => by rw [hhdr] at h; cases h)
  | some p =>
    rcases p with ⟨mv, nc, rest⟩
    intro j m0 hmv_bd hnc_bd hj hdrop hm0
    have hmv := hmv_bd; have hnc := hnc_bd
    unfold dimacsBound at hmv hnc
    wp_unfold
    have hm0_d : (dimacsState hdr_addr (BitVec.ofNat 64 mv) (BitVec.ofNat 64 nc)
        (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 nc) ⋆
        (bytes cnf_ptr cnfBytes ⋆
          region (hdr_addr + BitVec.ofNat 64 32) (avail.toNat - 32) ⋆ R)) m0 := sep_ac hm0
    refine ⟨_, load_dimacs_mv hm0_d, _, load_dimacs_nc hm0_d, ?_⟩
    have hfx_lt := fixedBytes_lt hmv_bd
    have hvb_lt : valsBytes mv < 2 ^ 34 := by unfold fixedBytes at hfx_lt; omega
    have hmb_lt : markBytes mv < 2 ^ 34 := by unfold fixedBytes at hfx_lt; omega
    have hub_lt : u32VarBytes mv < 2 ^ 34 := by unfold fixedBytes at hfx_lt; omega
    have hwb_lt : whBytes mv < 2 ^ 34 := by unfold fixedBytes at hfx_lt; omega
    have hshl1 : BitVec.ofNat 64 mv <<< (((1 : BitVec 32).signExtend 64).toNat % 64) =
        BitVec.ofNat 64 (2 * mv) := bv_shl_sext1 (n := mv)
    have hshl2 : BitVec.ofNat 64 mv <<< (((2 : BitVec 32).signExtend 64).toNat % 64) =
        BitVec.ofNat 64 (4 * mv) := bv_shl_sext2 (n := mv)
    have hshl2b : BitVec.ofNat 64 (2 * mv) <<< (((2 : BitVec 32).signExtend 64).toNat % 64) =
        BitVec.ofNat 64 (8 * mv) := by rw [bv_shl_sext2]; congr 1; omega
    rw [hshl1, hshl2, hshl2b,
      bv64_align8 (n := 2 * mv) (by omega), bv64_align8 (n := mv) (by omega),
      bv64_align8 (n := 4 * mv) (by omega), bv64_align8 (n := 8 * mv) (by omega)]
    have hfx_bv : (200 : BitVec 64) + BitVec.ofNat 64 (((2 * mv + 7) / 8) * 8) +
        BitVec.ofNat 64 (((mv + 7) / 8) * 8) +
        (BitVec.ofNat 64 (((4 * mv + 7) / 8) * 8) <<<
          (((2 : BitVec 32).signExtend 64).toNat % 64)) +
        BitVec.ofNat 64 (((8 * mv + 7) / 8) * 8) = BitVec.ofNat 64 (fixedBytes mv) := by
      rw [bv_shl_sext2, show (200 : BitVec 64) = BitVec.ofNat 64 200 from rfl,
        bv_add_ofNat, bv_add_ofNat, bv_add_ofNat, bv_add_ofNat]; rfl
    have hult_fx : avail.ult (BitVec.ofNat 64 (fixedBytes mv)) =
        decide (avail.toNat < fixedBytes mv) := by
      simpa [bv_ofNat_toNat_eq avail] using
        bv_ult_eq (a := avail.toNat) (b := fixedBytes mv) avail.isLt (by omega)
    rw [hfx_bv, hult_fx]
    simp only [decide_eq_true_eq, decide_eq_false_iff_not]
    refine ⟨fun hlt => hQfalse m0 (hremerge _ _ _ _ m0 hm0) (fun mv' nc' rest' h => by
        rw [hhdr] at h; rcases Option.some.inj h with ⟨rfl, rfl, rfl⟩; omega),
      fun hge_fx => ?_⟩
    have hrem_eq : avail - BitVec.ofNat 64 (fixedBytes mv) =
        BitVec.ofNat 64 (avail.toNat - fixedBytes mv) := by
      simpa [bv_ofNat_toNat_eq avail] using
        bv_sub_ofNat (a := avail.toNat) (b := fixedBytes mv) (by omega) avail.isLt
    let rem := avail.toNat - fixedBytes mv
    have hrem64 : rem < 2 ^ 64 := by omega
    rw [hrem_eq, bv64_mul24, bv_ult_eq hrem64 (by omega)]
    simp only [decide_eq_true_eq, decide_eq_false_iff_not]
    refine ⟨fun hlt => hQfalse m0 (hremerge _ _ _ _ m0 hm0) (fun mv' nc' rest' h => by
        rw [hhdr] at h; rcases Option.some.inj h with ⟨rfl, rfl, rfl⟩; omega),
      fun hge_mc => ?_⟩
    have hsub_mc : BitVec.ofNat 64 rem - BitVec.ofNat 64 (nc * 24) =
        BitVec.ofNat 64 (rem - nc * 24) := bv_sub_ofNat (by omega) hrem64
    rw [hsub_mc, bv_shr_sext6 (by omega), bv_add_ofNat]
    refine wp_join_group
      (fun (mc_v, ()) m1 => mc_v = BitVec.ofNat 64 (initMaxC nc rem) ∧ m1 = m0) ?_ ?_
    · rintro _ ⟨mc_v, ⟨⟩⟩ m1 ⟨rfl, hm1⟩
      subst m1
      wp_unfold
      have hmc_le : initMaxC nc rem * 24 ≤ rem := initMaxC_mul24_le (by omega)
      have hmc_lt : initMaxC nc rem < dimacsBound := initMaxC_lt
      unfold dimacsBound at hmc_lt
      rw [bv64_mul24, bv_sub_ofNat hmc_le hrem64, bv_shr_sext2 (by omega)]
      refine wp_join_group
        (fun (lc_v, ()) m2 => lc_v = BitVec.ofNat 64 (initLcap nc rem) ∧ m2 = m0) ?_ ?_
      · rintro _ ⟨lc_v, ⟨⟩⟩ m2 ⟨rfl, hm2⟩
        subst m2
        wp_unfold
        let c : ArenaCfg :=
          ⟨hdr_addr, avail.toNat, mv, nc, initMaxC nc rem, initLcap nc rem,
            hmv_bd, hnc_bd, initMaxC_lt, initLcap_lt, havel_fit, init_arena_fits (by omega)⟩
        have hc_hdr : c.hdr = hdr_addr := rfl
        have hc_av : c.avail = avail.toNat := rfl
        have hrem_split : (region (hdr_addr + BitVec.ofNat 64 32) (avail.toNat - 32) ⋆
            (bytes cnf_ptr cnfBytes ⋆
              dimacsState hdr_addr (BitVec.ofNat 64 mv) (BitVec.ofNat 64 nc)
                (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 nc) ⋆ R)) m0 := sep_ac hm0
        rw [← region_merge_eq (a := hdr_addr + BitVec.ofNat 64 32) (n1 := 168)
            (n2 := avail.toNat - 200) (n := avail.toNat - 32) (by omega) (by omega),
          ptr_add_ofNat, show (32 + 168 : Nat) = 200 from rfl] at hrem_split
        have h168_focus : (region (hdr_addr + BitVec.ofNat 64 32) 168 ⋆
            (region (hdr_addr + BitVec.ofNat 64 200) (avail.toNat - 200) ⋆
              (bytes cnf_ptr cnfBytes ⋆
                dimacsState hdr_addr (BitVec.ofNat 64 mv) (BitVec.ofNat 64 nc)
                  (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 nc) ⋆ R))) m0 := by
          rw [← sep_assoc]; exact hrem_split
        rcases h168_focus with ⟨m_hdr, m_rest2, hu_hr, hd_hr, h_hdr168, h_rest2⟩
        obtain ⟨ws, hwslen, h_arr64⟩ := region_to_array64 21 (by decide) h_hdr168
        rcases h_rest2 with ⟨m_arrs, m_cdr, hu_ac, hd_ac, h_reg200, h_cdr⟩
        obtain ⟨vals, mrk, lvl, rsns, trl, tmp, wh, cls, wn, lpool,
          hvl, hmkl, hll, hrsl, htrl, htmpl, hwhl, hclsl, hwnl, hlpl, h_arrs⟩ :=
          c.avail_to_arrays h_reg200
        have hm_arr64 : (array64 (c.hdr + 32) ws ⋆
            ((array (t := i8) c.pVals vals ⋆ array (t := i8) c.pMark mrk ⋆
              array (t := i32) c.pLevel lvl ⋆ array (t := i32) c.pReason rsns ⋆
              array (t := i32) c.pTrail trl ⋆ array (t := i32) c.pTmp tmp ⋆
              array (t := i32) c.pWh wh ⋆ array (t := i32) c.pClauses cls ⋆
              array (t := i32) c.pWn wn ⋆ array (t := i32) c.pLpool lpool ⋆ c.pad) ⋆
              (bytes cnf_ptr cnfBytes ⋆
                dimacsState hdr_addr (BitVec.ofNat 64 mv) (BitVec.ofNat 64 nc)
                  (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 nc) ⋆ R))) m0 :=
          ⟨m_hdr, m_rest2, hu_hr, hd_hr, h_arr64, m_arrs, m_cdr, hu_ac, hd_ac, h_arrs, h_cdr⟩
        have hst : ∀ (k : Nat) (v : BitVec 64) {xs : List (BitVec 64)} {F : Mem 64 → Prop} {mf},
            k < xs.length → (array64 (c.hdr + 32) xs ⋆ F) mf →
            storeOk mf i64 (c.hdr + BitVec.ofNat 64 (32 + 8 * k)) ∧
              (array64 (c.hdr + 32) (xs.set k v) ⋆ F)
                (storeMem mf i64 (c.hdr + BitVec.ofNat 64 (32 + 8 * k)) v) := by
          intro k v xs F mf hk hmf
          simpa [ptr_add_ofNat] using store_array64 (i := k) v hk hmf
        rw [bv_shl_sext4, show initMaxC nc rem * 24 = 24 * initMaxC nc rem by omega]
        obtain ⟨o4, hm4⟩ := hst 4 c.pVals (by simp [hwslen]) hm_arr64
        obtain ⟨o5, hm5⟩ := hst 5 c.pMark (by simp [hwslen]) hm4
        obtain ⟨o6, hm6⟩ := hst 6 c.pLevel (by simp [hwslen]) hm5
        obtain ⟨o7, hm7⟩ := hst 7 c.pReason (by simp [hwslen]) hm6
        obtain ⟨o8, hm8⟩ := hst 8 c.pTrail (by simp [hwslen]) hm7
        obtain ⟨o13, hm13⟩ := hst 13 c.pTmp (by simp [hwslen]) hm8
        obtain ⟨o9, hm9⟩ := hst 9 c.pWh (by simp [hwslen]) hm13
        obtain ⟨o10, hm10⟩ := hst 10 c.pClauses (by simp [hwslen]) hm9
        obtain ⟨o11, hm11⟩ := hst 11 c.pWn (by simp [hwslen]) hm10
        obtain ⟨o12, hm12⟩ := hst 12 c.pLpool (by simp [hwslen]) hm11
        obtain ⟨o0, hm0'⟩ := hst 0 (BitVec.ofNat 64 c.max_c) (by simp [hwslen]) hm12
        obtain ⟨o1, hm1'⟩ := hst 1 (BitVec.ofNat 64 c.lcap) (by simp [hwslen]) hm0'
        obtain ⟨o2, hm2'⟩ := hst 2 0#64 (by simp [hwslen]) hm1'
        obtain ⟨o3, hm3'⟩ := hst 3 0#64 (by simp [hwslen]) hm2'
        obtain ⟨o14, hm14⟩ := hst 14 0#64 (by simp [hwslen]) hm3'
        obtain ⟨o15, hm15⟩ := hst 15 0#64 (by simp [hwslen]) hm14
        obtain ⟨o16, hm16⟩ := hst 16 0#64 (by simp [hwslen]) hm15
        obtain ⟨o17, hm17⟩ := hst 17 fuel (by simp [hwslen]) hm16
        obtain ⟨o18, hm18⟩ := hst 18 0xFFFFFFFF#64 (by simp [hwslen]) hm17
        obtain ⟨o19, hm19⟩ := hst 19 0#64 (by simp [hwslen]) hm18
        obtain ⟨o20, hm20⟩ := hst 20 0#64 (by simp [hwslen]) hm19
        refine ⟨o4, o5, o6, o7, o8, o13, o9, o10, o11, o12, o0, o1, o2, o3,
          o14, o15, o16, o17, o18, o19, o20, ?_⟩
        let s_pre : ArenaState :=
          { d_cur := cnf_ptr + BitVec.ofNat 64 j, d_val := BitVec.ofNat 64 nc,
            lit_len := 0, num_clauses := 0, trail_end := 0, propagated := 0, cur_level := 0,
            fuel := fuel, confl_cid := 0xFFFFFFFF#64, tmp_cnt := 0, tmp_len := 0,
            vals := vals, mrk := mrk, lvl := lvl, rsns := rsns, trl := trl, tmp := tmp,
            wh := wh, cls := cls, wn := wn, lpool := lpool }
        have hws_eq : ((((((((((((((((((((ws.set 4 c.pVals).set 5 c.pMark).set 6 c.pLevel).set
            7 c.pReason).set 8 c.pTrail).set 13 c.pTmp).set 9 c.pWh).set 10 c.pClauses).set
            11 c.pWn).set 12 c.pLpool).set 0 (BitVec.ofNat 64 c.max_c)).set
            1 (BitVec.ofNat 64 c.lcap)).set 2 0#64).set 3 0#64).set 14 0#64).set 15 0#64).set
            16 0#64).set 17 fuel).set 18 0xFFFFFFFF#64).set 19 0#64).set 20 0#64 =
            hdrTailWords c s_pre := by
          apply List.ext_getElem (by simp [hwslen, hdrTailWords])
          intro k hk1 _
          have hk21 : k < 21 := by simp [hwslen] at hk1; exact hk1
          rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
            _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k
          · simp [hdrTailWords, s_pre]
          · simp [hdrTailWords, s_pre]
          · simp [hdrTailWords, s_pre]
          · simp [hdrTailWords, s_pre]
          · simp [hdrTailWords, s_pre]
          · simp [hdrTailWords, s_pre]
          · simp [hdrTailWords, s_pre]
          · simp [hdrTailWords, s_pre]
          · simp [hdrTailWords, s_pre]
          · simp [hdrTailWords, s_pre]
          · simp [hdrTailWords, s_pre]
          · simp [hdrTailWords, s_pre]
          · simp [hdrTailWords, s_pre]
          · simp [hdrTailWords, s_pre]
          · simp [hdrTailWords, s_pre]
          · simp [hdrTailWords, s_pre]
          · simp [hdrTailWords, s_pre]
          · simp [hdrTailWords, s_pre]
          · simp [hdrTailWords, s_pre]
          · simp [hdrTailWords, s_pre]
          · simp [hdrTailWords, s_pre]
          · omega
        rw [hws_eq] at hm20
        have hlen_pre : s_pre.LengthsOk c :=
          ⟨hvl, hmkl, hll, hrsl, htrl, htmpl, hwhl, hclsl, hwnl, hlpl,
            Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.le_refl _,
            by dsimp [s_pre]; omega, by dsimp [s_pre]; omega, by dsimp [s_pre]; omega⟩
        have hm_arena := (fun {mf} (hmf : (array64 (c.hdr + 32) (hdrTailWords c s_pre) ⋆
            ((array (t := i8) c.pVals vals ⋆ array (t := i8) c.pMark mrk ⋆
              array (t := i32) c.pLevel lvl ⋆ array (t := i32) c.pReason rsns ⋆
              array (t := i32) c.pTrail trl ⋆ array (t := i32) c.pTmp tmp ⋆
              array (t := i32) c.pWh wh ⋆ array (t := i32) c.pClauses cls ⋆
              array (t := i32) c.pWn wn ⋆ array (t := i32) c.pLpool lpool ⋆ c.pad) ⋆
              (bytes cnf_ptr cnfBytes ⋆
                dimacsState hdr_addr (BitVec.ofNat 64 mv) (BitVec.ofNat 64 nc)
                  (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 nc) ⋆ R))) mf) =>
            (by unfold ArenaMem; exact sep_ac hmf :
              (ArenaMem c s_pre ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) mf)) hm20
        apply wp_call_of_spec; apply hZero
        refine ⟨c, s_pre, bytes cnf_ptr cnfBytes ⋆ R, rfl, hlen_pre, hm_arena,
          fun m_z hm_z => ?_⟩
        wp_unfold
        let s0 : ArenaState :=
          { s_pre with
            vals := List.replicate (2 * c.mv) 0#8,
            wh := List.replicate (2 * c.mv) 0xFFFFFFFF#32,
            mrk := List.replicate c.mv 0#8,
            lvl := List.replicate c.mv 0#32,
            rsns := List.replicate c.mv 0xFFFFFFFF#32,
            tmp := List.replicate c.mv 0#32 }
        have hlen0 : s0.LengthsOk c :=
          ⟨by simp [s0], by simp [s0], by simp [s0], by simp [s0], htrl, by simp [s0],
            by simp [s0], hclsl, hwnl, hlpl, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _,
            Nat.le_refl _, by dsimp [s0, s_pre]; omega, by dsimp [s0, s_pre]; omega,
            by dsimp [s0, s_pre]; omega⟩
        have hm_z' : (ArenaMem c s0 ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m_z := hm_z
        exact hQtrue c s0 j rest m_z rfl rfl hhdr hj hdrop
          (solverInv_init hlen0 rfl rfl rfl rfl rfl rfl rfl)
          rfl rfl rfl rfl rfl rfl rfl rfl rfl (sep_ac hm_z')
      · intro J2 hJ2; wp_unfold
        rw [show (268435455 : BitVec 64) = BitVec.ofNat 64 (dimacsBound - 1) from rfl,
          bv_ult_eq (by decide) (by omega)]
        simp only [decide_eq_true_eq, decide_eq_false_iff_not]
        refine ⟨fun hgt => hJ2 _ m0 ⟨by
            unfold initLcap; rw [Nat.min_eq_right (by omega)], rfl⟩,
          fun hle => hJ2 _ m0 ⟨by
            unfold initLcap; rw [Nat.min_eq_left (by omega)], rfl⟩⟩
    · intro J1 hJ1; wp_unfold
      have hraw64 : nc + (rem - nc * 24) / 64 < 2 ^ 64 := by omega
      rw [show (268435455 : BitVec 64) = BitVec.ofNat 64 (dimacsBound - 1) from rfl,
        bv_ult_eq (by decide) hraw64]
      simp only [decide_eq_true_eq, decide_eq_false_iff_not]
      refine ⟨fun hgt => hJ1 _ m0 ⟨by
          unfold initMaxC; rw [Nat.min_eq_right (by omega)], rfl⟩,
        fun hle => hJ1 _ m0 ⟨by
          unfold initMaxC; rw [Nat.min_eq_left (by omega)], rfl⟩⟩

/-! ## 3. `kissat_skip_clause_syntax` specification and `Func.wp` proof -/

/-- Specification of `kissat_skip_clause_syntax(cnf_end, d)`. -/
def kissatSkipClauseSyntaxSpec : Spec [i64, i64] [.bool] := fun (cend, d, ()) m Q _ =>
  ∃ (cnf_ptr nc val0 : BitVec 64) (mv : Nat) (cnfBytes : List UInt8) (i0 : Nat)
    (R : Mem 64 → Prop),
    cend = cnf_ptr + BitVec.ofNat 64 cnfBytes.length ∧
    cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
    mv < 2 ^ 64 ∧
    i0 ≤ cnfBytes.length ∧
    (bytes cnf_ptr cnfBytes ⋆
      dimacsState d (BitVec.ofNat 64 mv) nc (cnf_ptr + BitVec.ofNat 64 i0) val0 ⋆ R) m ∧
    match parseClause mv (cnfBytes.drop i0) with
    | none =>
      ∀ cur' val' m',
        (bytes cnf_ptr cnfBytes ⋆ dimacsState d (BitVec.ofNat 64 mv) nc cur' val' ⋆ R) m' →
        Q (false, ()) m'
    | some (cl, rest) =>
      ∀ j m', (∀ lit ∈ cl.literals, 1 ≤ lit.1) → i0 < j → j ≤ cnfBytes.length →
        cnfBytes.drop j = rest →
        (bytes cnf_ptr cnfBytes ⋆
          dimacsState d (BitVec.ofNat 64 mv) nc (cnf_ptr + BitVec.ofNat 64 j) 0#64 ⋆ R) m' →
        Q (true, ()) m'

theorem kissat_skip_clause_syntax_wp (Γ : Env)
    (hLit : ∀ args m Q X, kissatNextLitSpec args m Q X →
      Γ "kissat_next_lit" [i64, i64] [i64] args m Q X) :
    ∀ args m Q X, kissatSkipClauseSyntaxSpec args m Q X →
      Func.wp Γ kissat_skip_clause_syntax_body args m Q X := by
  rintro ⟨cend, d, ⟨⟩⟩ m Q X ⟨cnf_ptr, nc, val0, mv, cnfBytes, i0, R, rfl, hfit, hmv64, hi0, hm, hQ⟩
  unfold Func.wp kissat_skip_clause_syntax_body; wp_unfold
  refine wp_loop_group
    (fun r () ml => ∃ idx val_l revLits,
      i0 ≤ idx ∧ idx ≤ cnfBytes.length ∧ r = cnfBytes.length - idx ∧
      (∀ lit ∈ revLits, 1 ≤ lit.1) ∧
      parseClauseAux ((cnfBytes.drop idx).length + 1) mv revLits (cnfBytes.drop idx) =
        parseClause mv (cnfBytes.drop i0) ∧
      (bytes cnf_ptr cnfBytes ⋆
        dimacsState d (BitVec.ofNat 64 mv) nc (cnf_ptr + BitVec.ofNat 64 idx) val_l ⋆ R) ml)
    ?_ ?_
  · rintro L r ⟨⟩ ml ih ⟨idx, val_l, revLits, hi_le, hidx, rfl, hpos_acc, hpc_inv, hml⟩
    wp_unfold
    apply wp_call_of_spec; apply hLit
    change kissatNextLitSpec (cnf_ptr + BitVec.ofNat 64 cnfBytes.length, d, ()) ml _ _
    refine ⟨cnf_ptr, nc, val_l, mv, cnfBytes, idx, R, rfl, hfit, hmv64, hidx, hml, ?_⟩
    cases hnl : nextLitPure mv (cnfBytes.drop idx) with
    | err =>
      intro cur' val' m' hm'
      wp_unfold
      refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
      have hnone : parseClause mv (cnfBytes.drop i0) = none := by
        rw [← hpc_inv, parseClauseAux_eq_nextLitPure, hnl]
      rw [hnone] at hQ
      exact hQ cur' val' m' hm'
    | endClause rest =>
      intro j m' hij hj hdrop hm'
      wp_unfold
      refine ⟨fun h => absurd h (by decide), fun _ => ⟨fun _ => ?_, fun h => absurd rfl h⟩⟩
      have hsome : parseClause mv (cnfBytes.drop i0) =
          some (CNF.Clause.ofLiterals revLits.reverse, rest) := by
        rw [← hpc_inv, parseClauseAux_eq_nextLitPure, hnl]
      rw [hsome] at hQ
      refine hQ j m' (fun lit hlit => ?_) (by omega) hj hdrop hm'
      simp only [CNF.Clause.literals_ofLiterals, List.mem_reverse] at hlit
      exact hpos_acc lit hlit
    | lit l rest =>
      intro j m' _ _ hij hj hdrop hm'
      wp_unfold
      refine ⟨fun h => absurd h (by decide), fun _ =>
        ⟨fun h => absurd h (by decide), fun _ => ?_⟩⟩
      refine ih (cnfBytes.length - j) () m' (by omega)
        ⟨j, BitVec.ofNat 64 l, kissatLitToDimacsLiteral l :: revLits,
          by omega, hj, rfl, fun lit hlit => (List.mem_cons.mp hlit).elim
            (fun h => h ▸ by simp [kissatLitToDimacsLiteral]) (hpos_acc lit), ?_, hm'⟩
      have hstep : parseClauseAux ((cnfBytes.drop idx).length + 1) mv revLits (cnfBytes.drop idx) =
          parseClauseAux (cnfBytes.drop idx).length mv (kissatLitToDimacsLiteral l :: revLits)
            (cnfBytes.drop j) := by
        rw [parseClauseAux_eq_nextLitPure, hnl, ← hdrop]
      rw [← hpc_inv, hstep]
      exact parseClauseAux_fuel_irrel (by simp) (by simp; omega)
  · intro L hL; wp_unfold
    exact hL (cnfBytes.length - i0) () m
      ⟨i0, val0, [], Nat.le_refl _, hi0, rfl, (fun _ h => by cases h), rfl, hm⟩

end LeanQbe.T.Examples.Kissat
