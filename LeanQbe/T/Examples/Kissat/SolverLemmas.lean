module

public import LeanQbe.T.Examples.Kissat.SolverIngestLemmas
public import LeanQbe.T.Examples.Kissat.SolverPropLemmas
public import LeanQbe.T.Examples.Kissat.SolverAnalyzeLemmas
import all Kraken.Mem
import all Kraken.Separation

/-!
# End-to-End Kissat `D-Min` C0 `kissat_solve_bytes` Verification

Assembles all 25 functions in `kissatFns = dimacs_fns ++ solver_fns` into a closed acyclic
`ModuleOk` proof for `kissatModule` and proves:
* `kissat_solve_bytes_core_wp` / `kissat_solve_bytes_wp`: full termination (`h->fuel.toNat`
  variant), read-only `[cnf_ptr, cnf_ptr + cnf_len)`, restored `region work_ptr work_len`,
  return code `r ∈ {0, 10, 20}`, UNSAT soundness (`r = 20 → ∃ cnf, parseDimacs = some cnf ∧
  cnf.Unsat`), SAT soundness (`r = 10 → ∃ cnf, parseDimacs = some cnf ∧ ¬ cnf.Unsat ∧
  ∃ α, cnf.Sat α`), and deterministic unit-clause witness traces;
* `mkKissatEnv`, `kissatEnv`, `kissatEnv_sound`, `kissatEnv_noExit`, `kissatEnv_moduleOk`,
  and headline `kissat_solve_bytes_correct`;
* concrete source-level UNSAT (`nvUnsatBytes` → `20#64`) and SAT (`nvSatBytes` → `10#64`)
  non-vacuity contracts (`kissatUnsatWitnessEnv`, `kissatSatWitnessEnv`) and payload framing
  lemmas ready for SysV x64 (`Amd64.Kissat`) and AAPCS64 (`Arm64.Kissat`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open Kraken.Bedrock2.Test

/-! ## 1. Pure DIMACS, conflict-soundness, bit-vector, and arena-framing helpers -/

private theorem parseClauses_vars_pos {mv : Nat} :
    ∀ {n : Nat} {acc : CNF Nat} {bs : List UInt8} {cnf : CNF Nat},
      CnfVarsPos acc → parseClauses mv n acc bs = some cnf → CnfVarsPos cnf
  | 0, acc, bs, cnf, hacc, h => by
    unfold parseClauses at h
    cases hsw : skipWsComments bs with
    | nil =>
      rw [hsw] at h
      cases Option.some.inj h
      exact hacc
    | cons _ _ => rw [hsw] at h; cases h
  | n + 1, acc, bs, cnf, hacc, h => by
    unfold parseClauses at h
    cases hpc : parseClause mv bs with
    | none => rw [hpc] at h; cases h
    | some p =>
      rcases p with ⟨cl, rest⟩
      rw [hpc] at h
      have hpos : ∀ lit ∈ cl.literals, 1 ≤ lit.1 :=
        parseClauseAux_vars_pos (by simp) hpc
      exact parseClauses_vars_pos (cnfVarsPos_add hacc hpos) h

private theorem parseDimacs_vars_pos {bs : List UInt8} {cnf : CNF Nat}
    (h : parseDimacs bs = some cnf) : CnfVarsPos cnf := by
  unfold parseDimacs at h
  cases hh : parseHeader bs with
  | none => rw [hh] at h; cases h
  | some p =>
    rcases p with ⟨mv, nc, rest⟩
    rw [hh] at h
    exact parseClauses_vars_pos (by intro _ hc; simp at hc) h

private theorem bv64_ugt_max_sub_false {p : BitVec 64} {n : Nat}
    (hfit : p.toNat + n < 2 ^ 64) :
    ((0xFFFFFFFFFFFFFFFF#64 - p).ult (BitVec.ofNat 64 n)) = false := by
  have hp := p.isLt
  have hmax : (0xFFFFFFFFFFFFFFFF#64 : BitVec 64).toNat = 2 ^ 64 - 1 := rfl
  have hsub : 0xFFFFFFFFFFFFFFFF#64 - p = BitVec.ofNat 64 (2 ^ 64 - 1 - p.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, hmax, bv64_ofNat_toNat (by omega)]
    omega
  rw [hsub, bv_ult_eq (by omega) (by omega)]
  simp only [decide_eq_false_iff_not]; omega

private theorem bv64_and7_toNat (p : BitVec 64) : (p &&& 7).toNat = p.toNat % 8 := by
  have h := BitVec.toNat_and p 7
  have h7 : (7 : BitVec 64).toNat = 7 := rfl
  rw [h7, Nat.and_two_pow_sub_one_eq_mod p.toNat 3] at h
  exact h

private theorem bv64_and7_eq_ofNat (p : BitVec 64) :
    p &&& 7 = BitVec.ofNat 64 (p.toNat % 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [bv64_and7_toNat, bv64_ofNat_toNat (by omega)]

private def alignPad (p : BitVec 64) : Nat :=
  if p.toNat % 8 = 0 then 0 else 8 - p.toNat % 8

private theorem alignPad_lt8 (p : BitVec 64) : alignPad p < 8 := by
  unfold alignPad; split <;> omega

private theorem bv64_sub_pad {w : Nat} {p : BitVec 64} (hle : alignPad p ≤ w) (hw : w < 2 ^ 64) :
    BitVec.ofNat 64 w - BitVec.ofNat 64 (alignPad p) = BitVec.ofNat 64 (w - alignPad p) :=
  bv_sub_ofNat hle hw

private def ArenaTail (c : ArenaCfg) (s : ArenaState) : Mem 64 → Prop :=
  array (t := i8) c.pMark s.mrk ⋆
  array (t := i32) c.pLevel s.lvl ⋆
  array (t := i32) c.pReason s.rsns ⋆
  array (t := i32) c.pTrail s.trl ⋆
  array (t := i32) c.pTmp s.tmp ⋆
  array (t := i32) c.pWh s.wh ⋆
  array (t := i32) c.pClauses s.cls ⋆
  array (t := i32) c.pWn s.wn ⋆
  array (t := i32) c.pLpool s.lpool ⋆
  c.pad

private def ArenaCheckRest (c : ArenaCfg) (s : ArenaState) : Mem 64 → Prop :=
  array64 (c.hdr + 32) (hdrTailWords c s) ⋆ ArenaTail c s

private theorem arenaMem_eq_check (c : ArenaCfg) (s : ArenaState) :
    ArenaMem c s =
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.d_cur s.d_val ⋆
        array64 (c.hdr + 32) (hdrTailWords c s) ⋆
        array (t := i8) c.pVals s.vals ⋆
        ArenaTail c s) := by
  unfold ArenaMem ArenaTail; simp only [sep_assoc]

private theorem arenaMem_to_checkModel {c : ArenaCfg} {s : ArenaState}
    {cnf_ptr : BitVec 64} {cnfBytes : List UInt8} {R : Mem 64 → Prop} {m : Mem 64}
    (hlen : s.LengthsOk c)
    (hm : (bytes cnf_ptr cnfBytes ⋆ ArenaMem c s ⋆ R) m) :
    (bytes cnf_ptr cnfBytes ⋆
      dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.d_cur s.d_val ⋆
      bytes c.pVals (s.vals.map UInt8.ofBitVec) ⋆
      (ArenaCheckRest c s ⋆ R)) m := by
  have hmv := c.hmv; unfold dimacsBound at hmv
  rw [arenaMem_eq_check] at hm
  have hm1 : (array (t := i8) c.pVals s.vals ⋆
      (bytes cnf_ptr cnfBytes ⋆
        dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.d_cur s.d_val ⋆
        (ArenaCheckRest c s ⋆ R))) m := by
    unfold ArenaCheckRest; exact sep_ac hm
  have hm2 : (bytes c.pVals (s.vals.map UInt8.ofBitVec) ⋆
      (bytes cnf_ptr cnfBytes ⋆
        dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.d_cur s.d_val ⋆
        (ArenaCheckRest c s ⋆ R))) m := by
    refine sep_mono (fun f hf => ?_) hm1
    have hbytes := array_eq_bytesOf (t := i8) c.pVals s.vals
      (by simp [Ty.bytes, Ty.size, i8, hlen.vals_len]; omega) hf
    rw [bytesOf_i8_eq_map] at hbytes
    exact hbytes.symm
  exact sep_ac hm2

private theorem checkModel_post_to_region {c : ArenaCfg} {s : ArenaState}
    {mv' nc' cur' val' : BitVec 64} {cnf_ptr : BitVec 64} {cnfBytes : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64} (hlen : s.LengthsOk c)
    (hm : (bytes cnf_ptr cnfBytes ⋆ dimacsState c.hdr mv' nc' cur' val' ⋆
      bytes c.pVals (s.vals.map UInt8.ofBitVec) ⋆ (ArenaCheckRest c s ⋆ R)) m) :
    (bytes cnf_ptr cnfBytes ⋆ region c.hdr c.avail ⋆ R) m := by
  have hmv := c.hmv; have hmc := c.hmax_c; have hlc := c.hlcap
  unfold dimacsBound at hmv hmc hlc
  unfold ArenaCheckRest at hm
  have hm1 : ((dimacsState c.hdr mv' nc' cur' val' ⋆
      array64 (c.hdr + 32) (hdrTailWords c s) ⋆
      bytes c.pVals (s.vals.map UInt8.ofBitVec) ⋆
      ArenaTail c s) ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m := sep_ac hm
  have hm2 : (region c.hdr c.avail ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m := by
    refine sep_mono (fun f hf => c.regions_to_avail ?_) hm1
    have hf' : (dimacsState c.hdr mv' nc' cur' val' ⋆
        array64 (c.hdr + 32) (hdrTailWords c s) ⋆
        bytes c.pVals (s.vals.map UInt8.ofBitVec) ⋆
        array (t := i8) c.pMark s.mrk ⋆
        array (t := i32) c.pLevel s.lvl ⋆
        array (t := i32) c.pReason s.rsns ⋆
        array (t := i32) c.pTrail s.trl ⋆
        array (t := i32) c.pTmp s.tmp ⋆
        array (t := i32) c.pWh s.wh ⋆
        array (t := i32) c.pClauses s.cls ⋆
        array (t := i32) c.pWn s.wn ⋆
        array (t := i32) c.pLpool s.lpool ⋆
        c.pad) f := by
      unfold ArenaTail at hf; simp only [sep_assoc] at hf ⊢; exact hf
    refine sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2
      (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2
        (fun _ h => dimacsState_to_region h)
        (fun _ h => by
          have h' := array_to_region (t := i64) (xs := hdrTailWords c s)
            (by simp [Ty.bytes, Ty.size, i64]) (by rwa [← array64_eq_array])
          simpa [Ty.bytes, Ty.size, i64] using h'))
        (fun _ h => by
          have h' := bytes_to_region h
          simpa [hlen.vals_len] using h'))
        (fun _ h => by
          have h' := array_to_region (t := i8)
            (by simp [Ty.bytes, Ty.size, i8, hlen.mrk_len]; omega) h
          simpa [Ty.bytes, Ty.size, i8, hlen.mrk_len] using h'))
        (fun _ h => by
          have h' := array_to_region (t := i32)
            (by simp [Ty.bytes, Ty.size, i32, hlen.lvl_len]; omega) h
          simpa [Ty.bytes, Ty.size, i32, hlen.lvl_len] using h'))
        (fun _ h => by
          have h' := array_to_region (t := i32)
            (by simp [Ty.bytes, Ty.size, i32, hlen.rsns_len]; omega) h
          simpa [Ty.bytes, Ty.size, i32, hlen.rsns_len] using h'))
        (fun _ h => by
          have h' := array_to_region (t := i32)
            (by simp [Ty.bytes, Ty.size, i32, hlen.trl_len]; omega) h
          simpa [Ty.bytes, Ty.size, i32, hlen.trl_len] using h'))
        (fun _ h => by
          have h' := array_to_region (t := i32)
            (by simp [Ty.bytes, Ty.size, i32, hlen.tmp_len_arr]; omega) h
          simpa [Ty.bytes, Ty.size, i32, hlen.tmp_len_arr] using h'))
        (fun _ h => by
          have h' := array_to_region (t := i32)
            (by simp [Ty.bytes, Ty.size, i32, hlen.wh_len]; omega) h
          have hmul : 4 * (2 * c.mv) = 8 * c.mv := by omega
          simpa [Ty.bytes, Ty.size, i32, hlen.wh_len, hmul] using h'))
        (fun _ h => by
          have h' := array_to_region (t := i32)
            (by simp [Ty.bytes, Ty.size, i32, hlen.cls_len]; omega) h
          have hmul : 4 * (4 * c.max_c) = 16 * c.max_c := by omega
          simpa [Ty.bytes, Ty.size, i32, hlen.cls_len, hmul] using h'))
        (fun _ h => by
          have h' := array_to_region (t := i32)
            (by simp [Ty.bytes, Ty.size, i32, hlen.wn_len]; omega) h
          have hmul : 4 * (2 * c.max_c) = 8 * c.max_c := by omega
          simpa [Ty.bytes, Ty.size, i32, hlen.wn_len, hmul] using h'))
        (fun _ h => by
          have h' := array_to_region (t := i32)
            (by simp [Ty.bytes, Ty.size, i32, hlen.lpool_len]; omega) h
          simpa [Ty.bytes, Ty.size, i32, hlen.lpool_len] using h'))
        (fun _ h => h) f hf'
  exact sep_ac hm2

/-! ## 2. `kissat_solve_bytes` core & top-level specifications and `Func.wp` proof -/

/-- Core specification of `kissat_solve_bytes` carrying both general soundness (`0 | 10 | 20`)
and deterministic unit-clause witness clauses for concrete UNSAT/SAT non-vacuity. -/
def kissatSolveBytesCoreSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
  fun (cnf_ptr, cnf_len, work_ptr, work_len, fuel, ()) m Q _ =>
    ∃ (cnfBytes : List UInt8) (wlen : Nat) (R : Mem 64 → Prop),
      cnf_len = BitVec.ofNat 64 cnfBytes.length ∧
      work_len = BitVec.ofNat 64 wlen ∧
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
      work_ptr.toNat + wlen < 2 ^ 64 ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m ∧
      ∀ r m',
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) →
        (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α) →
        (∀ mv nc i0,
          0 < fuel.toNat →
          fixedBytes mv + nc * 24 + 8 ≤ wlen →
          i0 ≤ cnfBytes.length →
          parseHeader cnfBytes = some (mv, nc, cnfBytes.drop i0) →
          UnitUnsatTrace mv (List.replicate (2 * mv) 0#8) (cnfBytes.drop i0) nc →
          r = 20#64) →
        (∀ mv nc i0 vals' te',
          te' < fuel.toNat →
          fixedBytes mv + nc * 24 + 8 ≤ wlen →
          i0 ≤ cnfBytes.length →
          parseHeader cnfBytes = some (mv, nc, cnfBytes.drop i0) →
          UnitSatTrace mv (List.replicate (2 * mv) 0#8) 0 (cnfBytes.drop i0) nc vals' te' →
          (∀ v < mv, vals'[2 * v]?.getD 0#8 ≠ 0#8) →
          runKissatCheckModel cnfBytes (vals'.map UInt8.ofBitVec) mv = true →
          r = 10#64) →
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' →
        Q (r, ()) m'

/-- Headline soundness specification of `kissat_solve_bytes`. -/
def kissatSolveBytesSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
  fun (cnf_ptr, cnf_len, work_ptr, work_len, _fuel, ()) m Q _ =>
    ∃ (cnfBytes : List UInt8) (wlen : Nat) (R : Mem 64 → Prop),
      cnf_len = BitVec.ofNat 64 cnfBytes.length ∧
      work_len = BitVec.ofNat 64 wlen ∧
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
      work_ptr.toNat + wlen < 2 ^ 64 ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m ∧
      ∀ r m',
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) →
        (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α) →
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' →
        Q (r, ()) m'

theorem kissatSolveBytesCoreSpec_of_spec
    {args : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : kissatSolveBytesSpec args m Q X) : kissatSolveBytesCoreSpec args m Q X := by
  obtain ⟨cnfBytes, wlen, R, hcl, hwl, hcfit, hwfit, hm, hQ⟩ := h
  exact ⟨cnfBytes, wlen, R, hcl, hwl, hcfit, hwfit, hm,
    fun r m' hdom hu hs _ _ hm' => hQ r m' hdom hu hs hm'⟩

theorem kissat_solve_bytes_core_wp (Γ : Env)
    (hInit : ∀ args m Q X, kissatInitStateSpec args m Q X →
      Γ "kissat_init_state" [i64, i64, i64, i64, i64] [.bool] args m Q X)
    (hParse : ∀ args m Q X, kissatParseBodySpec args m Q X →
      Γ "kissat_parse_body" [i64, i64] [i64] args m Q X)
    (hProp : ∀ args m Q X, kissatPropagateSpec args m Q X →
      Γ "kissat_propagate" [i64] [i64] args m Q X)
    (hAnalyze : ∀ args m Q X, kissatAnalyzeSpec args m Q X →
      Γ "kissat_analyze" [i64, i64] [i64] args m Q X)
    (hDecide : ∀ args m Q X, kissatDecideSpec args m Q X →
      Γ "kissat_decide" [i64] [i64] args m Q X)
    (hCheck : ∀ args m Q X, kissatCheckModelExactSpec args m Q X →
      Γ "kissat_check_model" [i64, i64, i64, i64, i64] [i64] args m Q X) :
    ∀ args m Q X, kissatSolveBytesCoreSpec args m Q X →
      Func.wp Γ kissat_solve_bytes_body args m Q X := by
  rintro ⟨cnf_ptr, cnf_len, work_ptr, work_len, fuel, ⟨⟩⟩ m Q X
    ⟨cnfBytes, wlen, R, rfl, rfl, hcfit, hwfit, hm, hQ⟩
  unfold Func.wp kissat_solve_bytes_body; wp_unfold
  -- 1. if (fuel == 0) return 0
  refine ⟨fun hf0 => ?_, fun hfne => ?_⟩
  · have hfz : fuel.toNat = 0 := by rw [hf0]; rfl
    exact hQ 0#64 m (Or.inl rfl) (fun h => by cases h) (fun h => by cases h)
      (fun _ _ _ hpos => by omega) (fun _ _ _ _ _ hlt => by omega) hm
  have hfpos : 0 < fuel.toNat :=
    Nat.pos_of_ne_zero fun h0 => hfne (BitVec.eq_of_toNat_eq (by simpa using h0))
  -- 2. if (cnf_len > ~0 - cnf_ptr || work_len > ~0 - work_ptr) return 0
  have hnot0 : ~~~(0 : BitVec 64) = 0xFFFFFFFFFFFFFFFF#64 := rfl
  rw [hnot0, bv64_ugt_max_sub_false hcfit]
  refine ⟨(fun h => by cases h), fun _ => ?_⟩
  rw [bv64_ugt_max_sub_false hwfit]
  refine ⟨(fun h => by cases h), fun _ => ?_⟩
  -- 3. mis = work_ptr & 7; pad = (mis == 0) ? 0 : (8 - mis)
  let pNat : Nat := alignPad work_ptr
  have hp_lt8 : pNat < 8 := alignPad_lt8 work_ptr
  refine wp_join_group (fun (pad_v, ()) m2 => pad_v = BitVec.ofNat 64 pNat ∧ m2 = m)
        (fun _ ⟨pad_v, ⟨⟩⟩ m2 ⟨hpad_v, hm2⟩ => by
          subst hpad_v m2; wp_unfold
          rw [show (200 : BitVec 64) = BitVec.ofNat 64 200 from rfl, bv_add_ofNat,
            bv_ult_eq (by omega) (by omega)]
          simp only [decide_eq_true_eq, decide_eq_false_iff_not]
          -- 4. if (work_len < pad + 200) return 0
          refine ⟨fun hw_small => ?_, fun hw_ok => ?_⟩
          · exact hQ 0#64 m (Or.inl rfl) (fun h => by cases h) (fun h => by cases h)
              (fun mv nc _ _ hsz _ _ _ => by unfold fixedBytes at hsz; omega)
              (fun mv nc _ _ _ _ hsz _ _ _ _ => by unfold fixedBytes at hsz; omega) hm
          · let hdr_addr : BitVec 64 := work_ptr + BitVec.ofNat 64 pNat
            let availNat : Nat := wlen - pNat
            have hav_eq : BitVec.ofNat 64 wlen - BitVec.ofNat 64 pNat =
                BitVec.ofNat 64 availNat := bv64_sub_pad (by omega) (by omega)
            rw [hav_eq]
            have hhdr_fit : hdr_addr.toNat + availNat < 2 ^ 64 := by
              rw [bv_add_ofNat_toNat (by omega)]; omega
            have hsplit : (bytes cnf_ptr cnfBytes ⋆
                region hdr_addr availNat ⋆ (region work_ptr pNat ⋆ R)) m := by
              have h1 : (region work_ptr wlen ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m := sep_ac hm
              rw [← region_merge_eq (a := work_ptr) (n1 := pNat) (n2 := availNat) (n := wlen)
                (by omega) (by omega)] at h1
              exact sep_ac h1
            have hmerge_reg : ∀ m',
                (bytes cnf_ptr cnfBytes ⋆ region hdr_addr availNat ⋆
                  (region work_ptr pNat ⋆ R)) m' →
                (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' := by
              intro m' hm'
              have h1 : ((region work_ptr pNat ⋆ region hdr_addr availNat) ⋆
                  (bytes cnf_ptr cnfBytes ⋆ R)) m' := sep_ac hm'
              have h2 : (region work_ptr (pNat + availNat) ⋆
                  (bytes cnf_ptr cnfBytes ⋆ R)) m' :=
                sep_mono (fun _ f => pad_region_merge (by omega) f) h1
              rw [show pNat + availNat = wlen by omega] at h2
              exact sep_ac h2
            have hmerge_arena : ∀ (c : ArenaCfg) (st : ArenaState) (m' : Mem 64),
                c.hdr = hdr_addr → c.avail = availNat → st.LengthsOk c →
                (bytes cnf_ptr cnfBytes ⋆ ArenaMem c st ⋆ (region work_ptr pNat ⋆ R)) m' →
                (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' := by
              intro c st m' hch hca hlen hm'
              apply hmerge_reg
              have h1 : (ArenaMem c st ⋆
                  (bytes cnf_ptr cnfBytes ⋆ region work_ptr pNat ⋆ R)) m' := sep_ac hm'
              have h2 : (region hdr_addr availNat ⋆
                  (bytes cnf_ptr cnfBytes ⋆ region work_ptr pNat ⋆ R)) m' :=
                sep_mono (fun _ f => by
                  rw [← hch, ← hca]; exact ArenaInv.to_region ⟨hlen, f⟩) h1
              exact sep_ac h2
            -- 5. if (!kissat_init_state(...)) return 0
            apply wp_call_of_spec; apply hInit
            dsimp only [kissatInitStateSpec, vals, Arg.val]
            refine ⟨cnfBytes, region work_ptr pNat ⋆ R, rfl, hcfit,
              by simpa [hdr_addr, bv64_ofNat_toNat (by omega : availNat < 2 ^ 64)] using hhdr_fit,
              by rw [bv64_ofNat_toNat (by omega)]; omega,
              by simpa [bv64_ofNat_toNat (by omega : availNat < 2 ^ 64)] using hsplit, ?_, ?_⟩
            · intro m' hm' hfail
              wp_unfold
              have hm'_r : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' :=
                hmerge_reg m'
                  (by simpa [bv64_ofNat_toNat (by omega : availNat < 2 ^ 64)] using hm')
              refine hQ 0#64 m' (Or.inl rfl) (fun h => by cases h) (fun h => by cases h)
                (fun mv nc i0 _ hsz _ hhdr _ => by
                  have hlt := hfail mv nc (cnfBytes.drop i0) hhdr
                  rw [bv64_ofNat_toNat (by omega)] at hlt; omega)
                (fun mv nc i0 _ _ _ hsz _ hhdr _ _ _ => by
                  have hlt := hfail mv nc (cnfBytes.drop i0) hhdr
                  rw [bv64_ofNat_toNat (by omega)] at hlt; omega) hm'_r
            · intro c s0 j0 rest0 m0 hch hca0 hhdr0 hj0 hdrop0 hinv0 hdcur0
                hll0 hnc0 hte0 hpr0 hcl0 hfu0 hvals0 hwh0 hm0
              have hca : c.avail = availNat := by
                rw [hca0, bv64_ofNat_toNat (by omega)]
              wp_unfold
              rw [← hch]
              -- 6. pst = kissat_parse_body(h, cnf_end)
              apply wp_call_of_spec; apply hParse
              refine ⟨c, s0, cnf_ptr, cnfBytes, j0, region work_ptr pNat ⋆ R,
                rfl, rfl, hcfit, hj0, by rwa [hdrop0], hdcur0, hcl0, hte0, hpr0, hnc0,
                hinv0, hm0, ?_⟩
              intro pst s1 m1 hlen1 hpst_dom hfu1 hpst20 hpst1 hsat_tr huns_tr hm1
              wp_unfold
              -- if (pst == 0) return 0
              refine ⟨fun hp0 => ?_, fun hpne0 => ?_⟩
              · refine hQ 0#64 m1 (Or.inl rfl) (fun h => by cases h) (fun h => by cases h)
                  (fun mv nc i0 _ _ _ hhdr hut => by
                    rw [hhdr0] at hhdr
                    rcases Prod.mk.inj (Option.some.inj hhdr) with ⟨rfl, hnc_rest⟩
                    rcases Prod.mk.inj hnc_rest with ⟨rfl, hrest_eq⟩
                    have h20 := huns_tr (by rw [hvals0, hdrop0, hrest_eq]; exact hut)
                    rw [hp0] at h20; cases h20)
                  (fun mv nc i0 vals' te' _ _ _ hhdr hst _ _ => by
                    rw [hhdr0] at hhdr
                    rcases Prod.mk.inj (Option.some.inj hhdr) with ⟨rfl, hnc_rest⟩
                    rcases Prod.mk.inj hnc_rest with ⟨rfl, hrest_eq⟩
                    have h1 := (hsat_tr vals' te'
                      (by rw [hvals0, hdrop0, hrest_eq]; exact hst)).1
                    rw [hp0] at h1; cases h1)
                  (hmerge_arena c s1 m1 hch hca hlen1 hm1)
              -- if (pst == 20) return 20
              refine ⟨fun hp20 => ?_, fun hpne20 => ?_⟩
              · refine hQ 20#64 m1 (Or.inr (Or.inr rfl)) (fun _ => hpst20 hp20)
                  (fun h => by cases h) (fun _ _ _ _ _ _ _ _ => rfl)
                  (fun mv nc i0 vals' te' _ _ _ hhdr hst _ _ => by
                    rw [hhdr0] at hhdr
                    rcases Prod.mk.inj (Option.some.inj hhdr) with ⟨rfl, hnc_rest⟩
                    rcases Prod.mk.inj hnc_rest with ⟨rfl, hrest_eq⟩
                    have h1 := (hsat_tr vals' te'
                      (by rw [hvals0, hdrop0, hrest_eq]; exact hst)).1
                    rw [hp20] at h1; cases h1)
                  (hmerge_arena c s1 m1 hch hca hlen1 hm1)
              have hpst_eq1 : pst = 1#64 := by
                rcases hpst_dom with h | h | h
                · exact absurd h hpne0
                · exact h
                · exact absurd h hpne20
              obtain ⟨cnf, hparse, hinv1, _⟩ := hpst1 hpst_eq1
              have hcnf_pos : CnfVarsPos cnf := parseDimacs_vars_pos hparse
              -- 7. Main CDCL while (true) loop, variant = st.fuel.toNat
              let SatFast (st : ArenaState) : Prop :=
                ∀ vals' te',
                  te' < fuel.toNat →
                  UnitSatTrace c.mv (List.replicate (2 * c.mv) 0#8) 0
                    (cnfBytes.drop j0) c.nc vals' te' →
                  (∀ v < c.mv, vals'[2 * v]?.getD 0#8 ≠ 0#8) →
                  runKissatCheckModel cnfBytes (vals'.map UInt8.ofBitVec) c.mv = true →
                  st.vals = vals' ∧ st.trail_end = te' ∧ st.propagated = 0 ∧
                  st.wh = List.replicate (2 * c.mv) 0xFFFFFFFF#32 ∧ st.fuel = fuel
              have hnot_unsat_trace :
                  ¬ UnitUnsatTrace c.mv (List.replicate (2 * c.mv) 0#8) (cnfBytes.drop j0) c.nc :=
                fun hut => by
                  have h20 := huns_tr (by rwa [hvals0])
                  rw [hpst_eq1] at h20; cases h20
              refine wp_loop_break_group
                (fun (res_v, ()) mb =>
                  (res_v = 0#64 ∨ res_v = 10#64 ∨ res_v = 20#64) ∧
                  (res_v = 20#64 → cnf.Unsat) ∧
                  (res_v = 10#64 → ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α) ∧
                  (∀ vals' te',
                    te' < fuel.toNat →
                    UnitSatTrace c.mv (List.replicate (2 * c.mv) 0#8) 0
                      (cnfBytes.drop j0) c.nc vals' te' →
                    (∀ v < c.mv, vals'[2 * v]?.getD 0#8 ≠ 0#8) →
                    runKissatCheckModel cnfBytes (vals'.map UInt8.ofBitVec) c.mv = true →
                    res_v = 10#64) ∧
                  (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) mb)
                (fun rem () ml => ∃ st : ArenaState,
                  rem = st.fuel.toNat ∧
                  SolverInv c (shiftDownCnf cnf) st ∧
                  SatFast st ∧
                  (bytes cnf_ptr cnfBytes ⋆ ArenaMem c st ⋆
                    (region work_ptr pNat ⋆ R)) ml) ?_ ?_ ?_
              · rintro _ ⟨res_v, ⟨⟩⟩ mb ⟨hdom, hu, hs, hsf, hmb⟩
                wp_unfold
                exact hQ res_v mb hdom
                  (fun h20 => ⟨cnf, hparse, hu h20⟩)
                  (fun h10 => ⟨cnf, hparse, hs h10⟩)
                  (fun mv nc i0 _ _ _ hhdr hut => by
                    rw [hhdr0] at hhdr
                    rcases Prod.mk.inj (Option.some.inj hhdr) with ⟨rfl, hnc_rest⟩
                    rcases Prod.mk.inj hnc_rest with ⟨rfl, hrest_eq⟩
                    exact absurd (by rwa [hdrop0, hrest_eq]) hnot_unsat_trace)
                  (fun mv nc i0 vals' te' hte _ _ hhdr hst hnz hcm => by
                    rw [hhdr0] at hhdr
                    rcases Prod.mk.inj (Option.some.inj hhdr) with ⟨rfl, hnc_rest⟩
                    rcases Prod.mk.inj hnc_rest with ⟨rfl, hrest_eq⟩
                    exact hsf vals' te' hte (by rwa [hdrop0, hrest_eq]) hnz hcm) hmb
              · rintro B L rem ⟨⟩ ml hB ih ⟨st, rfl, hst_inv, hsf, hml⟩
                wp_unfold
                have hml_a : (ArenaMem c st ⋆
                    (bytes cnf_ptr cnfBytes ⋆ region work_ptr pNat ⋆ R)) ml := sep_ac hml
                -- pr = kissat_propagate(h)
                apply wp_call_of_spec; apply hProp
                refine ⟨c, shiftDownCnf cnf, st,
                  bytes cnf_ptr cnfBytes ⋆ region work_ptr pNat ⋆ R,
                  rfl, hst_inv, hml_a, ?_⟩
                intro pr s2 m2 hs2_inv _ _ _ _ hpr_dom _ hpr1 hpr_empty hm2
                wp_unfold
                have hm2_b : (bytes cnf_ptr cnfBytes ⋆ ArenaMem c s2 ⋆
                    (region work_ptr pNat ⋆ R)) m2 := sep_ac hm2
                have hsf_prop : ∀ vals' te',
                    te' < fuel.toNat →
                    UnitSatTrace c.mv (List.replicate (2 * c.mv) 0#8) 0
                      (cnfBytes.drop j0) c.nc vals' te' →
                    (∀ v < c.mv, vals'[2 * v]?.getD 0#8 ≠ 0#8) →
                    runKissatCheckModel cnfBytes (vals'.map UInt8.ofBitVec) c.mv = true →
                    pr = 0#64 ∧ s2.vals = vals' ∧ s2.fuel.toNat = fuel.toNat - te' := by
                  intro vals' te' hte hst hnz hcm
                  obtain ⟨hvs, htes, hprs, hwhs, hfus⟩ := hsf vals' te' hte hst hnz hcm
                  have hempty : ∀ l < 2 * c.mv,
                      st.wh[l]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 := by
                    intro l hl; rw [hwhs, List.getElem?_replicate]; simp [hl]
                  have hres := hpr_empty hempty (by rw [htes, hprs, hfus]; omega)
                  exact ⟨hres.1, by rw [hres.2.1, hvs],
                    by rw [hres.2.2.2, htes, hprs, hfus]; omega⟩
                -- if (pr == 2) { res = 0; break; }
                refine ⟨fun hpr2 => ?_, fun hprne2 => ?_⟩
                · exact hB (0#64, ()) m2 ⟨Or.inl rfl, (fun h => by cases h),
                    (fun h => by cases h),
                    (fun vals' te' hte hst hnz hcm => by
                      have h0 := (hsf_prop vals' te' hte hst hnz hcm).1
                      rw [hpr2] at h0; cases h0),
                    hmerge_arena c s2 m2 hch hca hs2_inv.core.lengths hm2_b⟩
                -- if (pr == 1) { ... } else { ... }
                refine wp_join_group
                  (fun (_res, ()) m_next => ∃ s_next : ArenaState,
                    s_next.fuel.toNat < st.fuel.toNat ∧
                    SolverInv c (shiftDownCnf cnf) s_next ∧
                    SatFast s_next ∧
                    (bytes cnf_ptr cnfBytes ⋆ ArenaMem c s_next ⋆
                      (region work_ptr pNat ⋆ R)) m_next)
                  (fun _ ⟨_res, ⟨⟩⟩ m_next ⟨s_next, hlt_next, hinv_next, hsf_next, hm_next⟩ => by
                    wp_unfold
                    exact ih s_next.fuel.toNat () m_next hlt_next
                      ⟨s_next, rfl, hinv_next, hsf_next, hm_next⟩)
                  (fun J2 hJ2 => by
                    wp_unfold
                    refine ⟨fun hpr1_eq => ?_, fun hprne1 => ?_⟩
                    · obtain ⟨hfuel_lt, hcid_lt, hfals⟩ := hpr1 hpr1_eq
                      have hsf_false : ∀ vals' te',
                          te' < fuel.toNat →
                          UnitSatTrace c.mv (List.replicate (2 * c.mv) 0#8) 0
                            (cnfBytes.drop j0) c.nc vals' te' →
                          (∀ v < c.mv, vals'[2 * v]?.getD 0#8 ≠ 0#8) →
                          runKissatCheckModel cnfBytes (vals'.map UInt8.ofBitVec) c.mv = true →
                          False := fun vals' te' hte hst hnz hcm => by
                        have h0 := (hsf_prop vals' te' hte hst hnz hcm).1
                        rw [hpr1_eq] at h0; cases h0
                      refine ⟨_, load_arena_cur_level hm2, ?_⟩
                      have hcl_lt := hs2_inv.core.lengths.cur_level_lt
                      have hcl0_iff :
                          BitVec.ofNat 64 s2.cur_level = (0 : BitVec 64) ↔ s2.cur_level = 0 := by
                        constructor
                        · intro h
                          have ht := congrArg BitVec.toNat h
                          rwa [bv64_ofNat_toNat (by omega)] at ht
                        · intro h; rw [h]; rfl
                      rw [hcl0_iff]
                      refine ⟨fun hcl0 => ?_, fun hclne0 => ?_⟩
                      · have huns_sd := hs2_inv.core.level0_unsat_of_conflict hcl0 hcid_lt hfals
                        have huns := shiftDownCnf_unsat hcnf_pos huns_sd
                        exact hB (20#64, ()) m2 ⟨Or.inr (Or.inr rfl), fun _ => huns,
                          (fun h => by cases h),
                          fun vals' te' hte hst hnz hcm =>
                            (hsf_false vals' te' hte hst hnz hcm).elim,
                          hmerge_arena c s2 m2 hch hca hs2_inv.core.lengths hm2_b⟩
                      · refine ⟨_, load_arena_confl_cid hm2, ?_⟩
                        apply wp_call_of_spec; apply hAnalyze
                        refine ⟨c, shiftDownCnf cnf, s2,
                          bytes cnf_ptr cnfBytes ⋆ region work_ptr pNat ⋆ R,
                          rfl, hs2_inv, hcid_lt, hfals, hm2, ?_⟩
                        intro ast s3 m3 hlen3 hast_dom _ _ hfu3 hast20 hast1 hm3
                        wp_unfold
                        have hm3_b : (bytes cnf_ptr cnfBytes ⋆ ArenaMem c s3 ⋆
                            (region work_ptr pNat ⋆ R)) m3 := sep_ac hm3
                        refine ⟨fun ha20 => ?_, fun hane20 => ?_⟩
                        · have huns := shiftDownCnf_unsat hcnf_pos (hast20 ha20)
                          exact hB (20#64, ()) m3 ⟨Or.inr (Or.inr rfl), fun _ => huns,
                            (fun h => by cases h),
                            fun vals' te' hte hst hnz hcm =>
                              (hsf_false vals' te' hte hst hnz hcm).elim,
                            hmerge_arena c s3 m3 hch hca hlen3 hm3_b⟩
                        · refine ⟨fun hane1 => ?_, fun ha1 => ?_⟩
                          · exact hB (0#64, ()) m3 ⟨Or.inl rfl, (fun h => by cases h),
                              (fun h => by cases h),
                              fun vals' te' hte hst hnz hcm =>
                                (hsf_false vals' te' hte hst hnz hcm).elim,
                              hmerge_arena c s3 m3 hch hca hlen3 hm3_b⟩
                          · exact hJ2 _ m3 ⟨s3, by rw [hfu3]; exact hfuel_lt, hast1 ha1,
                              fun vals' te' hte hst hnz hcm =>
                                (hsf_false vals' te' hte hst hnz hcm).elim,
                              hm3_b⟩
                    · -- pr == 0: check fuel, decrement, decide, optionally check_model
                      refine ⟨_, load_arena_fuel hm2, ?_⟩
                      refine ⟨fun hf2_0 => ?_, fun hf2_ne => ?_⟩
                      · exact hB (0#64, ()) m2 ⟨Or.inl rfl, (fun h => by cases h),
                          (fun h => by cases h),
                          (fun vals' te' hte hst hnz hcm => by
                            have hrem := (hsf_prop vals' te' hte hst hnz hcm).2.2
                            have hfz2 : s2.fuel.toNat = 0 := by rw [hf2_0]; rfl
                            omega),
                          hmerge_arena c s2 m2 hch hca hs2_inv.core.lengths hm2_b⟩
                      · have hf2_pos : 0 < s2.fuel.toNat :=
                          Nat.pos_of_ne_zero fun h0 =>
                            hf2_ne (BitVec.eq_of_toNat_eq (by simpa using h0))
                        have hf2_sub : (s2.fuel - 1).toNat = s2.fuel.toNat - 1 :=
                          bv64_sub1_toNat hf2_ne
                        refine ⟨_, load_arena_fuel hm2, ?_⟩
                        obtain ⟨okf, hmf⟩ := store_arena_fuel (s2.fuel - 1) hm2
                        refine ⟨okf, ?_⟩
                        let s2' : ArenaState := { s2 with fuel := s2.fuel - 1 }
                        have hs2'_inv : SolverInv c (shiftDownCnf cnf) s2' :=
                          ⟨⟨⟨hs2_inv.core.lengths.vals_len, hs2_inv.core.lengths.mrk_len,
                              hs2_inv.core.lengths.lvl_len, hs2_inv.core.lengths.rsns_len,
                              hs2_inv.core.lengths.trl_len, hs2_inv.core.lengths.tmp_len_arr,
                              hs2_inv.core.lengths.wh_len, hs2_inv.core.lengths.cls_len,
                              hs2_inv.core.lengths.wn_len, hs2_inv.core.lengths.lpool_len,
                              hs2_inv.core.lengths.lit_len_le, hs2_inv.core.lengths.num_clauses_le,
                              hs2_inv.core.lengths.trail_end_le, hs2_inv.core.lengths.propagated_le,
                              hs2_inv.core.lengths.cur_level_lt, hs2_inv.core.lengths.tmp_cnt_lt,
                              hs2_inv.core.lengths.tmp_len_lt⟩,
                            ⟨hs2_inv.core.clauses.bounds, hs2_inv.core.clauses.disjoint,
                              hs2_inv.core.clauses.lits_lt, hs2_inv.core.clauses.entails⟩,
                            hs2_inv.core.cur_level_le,
                            hs2_inv.core.trail_lits_lt, hs2_inv.core.trail_vars_nodup,
                            hs2_inv.core.vals_domain, hs2_inv.core.vals_true_iff,
                            hs2_inv.core.vals_false_iff, hs2_inv.core.lvl_le,
                            hs2_inv.core.trail_mono, hs2_inv.core.levels_inhabited,
                            hs2_inv.core.level0_sound, hs2_inv.core.reason_inv⟩, hs2_inv.marks⟩
                        apply wp_call_of_spec; apply hDecide
                        refine ⟨c, shiftDownCnf cnf, s2',
                          bytes cnf_ptr cnfBytes ⋆ region work_ptr pNat ⋆ R,
                          rfl, hs2'_inv, hmf, ?_⟩
                        intro dst s3 m3 hs3_inv _ _ hfu3 hdst_dom hdst0 hdst_all hm3
                        wp_unfold
                        have hm3_b : (bytes cnf_ptr cnfBytes ⋆ ArenaMem c s3 ⋆
                            (region work_ptr pNat ⋆ R)) m3 := sep_ac hm3
                        refine ⟨fun hdst_eq0 => ?_, fun hdst_ne0 => ?_⟩
                        · -- dst == 0: call kissat_check_model
                          refine ⟨_, load_arena_values hm3, _, load_arena_mv hm3, ?_⟩
                          have hmv_bd := c.hmv; unfold dimacsBound at hmv_bd
                          have hcm_mem := arenaMem_to_checkModel hs3_inv.core.lengths hm3_b
                          apply wp_call_of_spec; apply hCheck
                          refine ⟨BitVec.ofNat 64 c.mv, BitVec.ofNat 64 c.nc, s3.d_cur, s3.d_val,
                            cnfBytes, s3.vals.map UInt8.ofBitVec, c.mv,
                            ArenaCheckRest c s3 ⋆ (region work_ptr pNat ⋆ R),
                            rfl, rfl, hcfit, by omega,
                            by simp [hs3_inv.core.lengths.vals_len],
                            by simp [hs3_inv.core.lengths.vals_len]; omega,
                            by simpa [sep_assoc] using hcm_mem, ?_⟩
                          intro ok mv' nc' cur' val' m4 hok hm4
                          have hm4_reg : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m4 :=
                            hmerge_reg m4 (by
                              dsimp only [hdr_addr]
                              rw [← hch, ← hca]
                              exact checkModel_post_to_region hs3_inv.core.lengths
                                (by simpa [sep_assoc] using hm4))
                          refine wp_join_group
                            (fun (res_v, ()) m5 =>
                              res_v = (if ok = 1#64 then 10#64 else 0#64) ∧ m5 = m4)
                            (fun _ ⟨res_v, ⟨⟩⟩ m5 ⟨hres_v, hm5⟩ => by
                              subst hres_v m5; wp_unfold
                              cases hrun : runKissatCheckModel cnfBytes
                                  (s3.vals.map UInt8.ofBitVec) c.mv with
                              | false =>
                                rw [hrun] at hok
                                simp only [Bool.false_eq_true, ↓reduceIte] at hok
                                subst hok
                                refine hB (0#64, ()) m4 ⟨Or.inl rfl, (fun h => by cases h),
                                  (fun h => by cases h), ?_, hm4_reg⟩
                                intro vals' te' hte hst hnz hcm
                                have hvs2 := (hsf_prop vals' te' hte hst hnz hcm).2.1
                                have hs3_eq := hdst0 hdst_eq0
                                have hvs3 : s3.vals = vals' := by rw [hs3_eq]; exact hvs2
                                rw [hvs3, hcm] at hrun; cases hrun
                              | true =>
                                rw [hrun] at hok; simp only [↓reduceIte] at hok; subst hok
                                obtain ⟨cnf', _, hparse', _, hnu, hsat⟩ :=
                                  runKissatCheckModel_sound hrun
                                rw [hparse] at hparse'
                                have hce : cnf = cnf' := Option.some.inj hparse'
                                subst hce
                                exact hB (10#64, ()) m4 ⟨Or.inr (Or.inl rfl),
                                  (fun h => by cases h), fun _ => ⟨hnu, hsat⟩,
                                  fun _ _ _ _ _ _ => rfl, hm4_reg⟩)
                            (fun Jr hJr => by
                              wp_unfold
                              exact ⟨fun h1 => hJr (10#64, ()) m4 ⟨by simp [h1], rfl⟩,
                                fun hne => by
                                  have hne' : ok ≠ 1#64 := hne
                                  exact hJr (0#64, ()) m4 ⟨by simp [hne'], rfl⟩⟩)
                        · -- dst == 1: loop with strictly smaller fuel
                          have hfu_lt : s3.fuel.toNat < st.fuel.toNat := by
                            rw [hfu3]; dsimp only [s2']; rw [hf2_sub]; omega
                          exact hJ2 _ m3 ⟨s3, hfu_lt, hs3_inv,
                            fun vals' te' hte hst hnz hcm => by
                              have hvs2 := (hsf_prop vals' te' hte hst hnz hcm).2.1
                              have h0 := (hdst_all (by dsimp only [s2']; rw [hvs2]; exact hnz)).1
                              exact absurd h0 hdst_ne0,
                            hm3_b⟩)
              · intro B L _ hL; wp_unfold
                refine hL s1.fuel.toNat () m1 ⟨s1, rfl, hinv1, ?_, hm1⟩
                intro vals' te' _ hst _ _
                obtain ⟨_, hvs, htes, hprs, _, hwhs⟩ :=
                  hsat_tr vals' te' (by rwa [hvals0])
                exact ⟨hvs, htes, hprs, by rw [hwhs, hwh0], by rw [hfu1, hfu0]⟩)
        (fun Jp hJp => by
          wp_unfold
          rw [bv64_and7_eq_ofNat work_ptr]
          have hmod0 :
              BitVec.ofNat 64 (work_ptr.toNat % 8) = (0 : BitVec 64) ↔ work_ptr.toNat % 8 = 0 := by
            constructor
            · intro h; have ht := congrArg BitVec.toNat h
              rwa [bv64_ofNat_toNat (by omega)] at ht
            · intro h; rw [h]; rfl
          rw [hmod0]
          refine ⟨fun hm0 => hJp (0#64, ()) m ⟨by simp [pNat, alignPad, hm0], rfl⟩,
            fun hmne => ?_⟩
          have hsub : (8 : BitVec 64) - BitVec.ofNat 64 (work_ptr.toNat % 8) =
              BitVec.ofNat 64 (8 - work_ptr.toNat % 8) :=
            bv_sub_ofNat (a := 8) (b := work_ptr.toNat % 8) (by omega) (by decide)
          exact hJp _ m ⟨by rw [hsub]; simp [pNat, alignPad, hmne], rfl⟩)

theorem kissat_solve_bytes_wp (Γ : Env)
    (hInit : ∀ args m Q X, kissatInitStateSpec args m Q X →
      Γ "kissat_init_state" [i64, i64, i64, i64, i64] [.bool] args m Q X)
    (hParse : ∀ args m Q X, kissatParseBodySpec args m Q X →
      Γ "kissat_parse_body" [i64, i64] [i64] args m Q X)
    (hProp : ∀ args m Q X, kissatPropagateSpec args m Q X →
      Γ "kissat_propagate" [i64] [i64] args m Q X)
    (hAnalyze : ∀ args m Q X, kissatAnalyzeSpec args m Q X →
      Γ "kissat_analyze" [i64, i64] [i64] args m Q X)
    (hDecide : ∀ args m Q X, kissatDecideSpec args m Q X →
      Γ "kissat_decide" [i64] [i64] args m Q X)
    (hCheck : ∀ args m Q X, kissatCheckModelExactSpec args m Q X →
      Γ "kissat_check_model" [i64, i64, i64, i64, i64] [i64] args m Q X) :
    ∀ args m Q X, kissatSolveBytesSpec args m Q X →
      Func.wp Γ kissat_solve_bytes_body args m Q X :=
  fun args m Q X h =>
    kissat_solve_bytes_core_wp Γ hInit hParse hProp hAnalyze hDecide hCheck args m Q X
      (kissatSolveBytesCoreSpec_of_spec h)

/-! ## 3. Closed 25-function module environment (`mkKissatEnv`, `kissatEnv`, `ModuleOk`) -/

/-- Parameterized specification environment covering all 25 functions in `kissatFns`. -/
def mkKissatEnv (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) : Env
  | "kissat_assign", [.bits 64, .bits 32, .bits 32], [] => kissatAssignSpec
  | "kissat_add_watch", [.bits 64, .bits 32, .bits 32], [] => kissatAddWatchSpec
  | "kissat_add_clause", [.bits 64, .bits 32], [.bits 64] => kissatAddClauseSpec
  | "kissat_backtrack", [.bits 64, .bits 64], [] => kissatBacktrackSpec
  | "kissat_zero_tables", [.bits 64], [] => kissatZeroTablesSpec
  | "kissat_init_state", [.bits 64, .bits 64, .bits 64, .bits 64, .bits 64], [.bool] =>
      kissatInitStateSpec
  | "kissat_skip_clause_syntax", [.bits 64, .bits 64], [.bool] => kissatSkipClauseSyntaxSpec
  | "kissat_ingest_clause", [.bits 64, .bits 64], [.bits 64] => kissatIngestClauseSpec
  | "kissat_parse_body", [.bits 64, .bits 64], [.bits 64] => kissatParseBodySpec
  | "kissat_find_repl", [.bits 64, .bits 64, .bits 32, .bits 32, .bits 64], [.bits 32] =>
      kissatFindReplSpec
  | "kissat_propagate_lit", [.bits 64, .bits 32], [.bits 64] => kissatPropagateLitSpec
  | "kissat_propagate", [.bits 64], [.bits 64] => kissatPropagateSpec
  | "kissat_analyze_clause", [.bits 64, .bits 32, .bits 32], [.bool] => kissatAnalyzeClauseSpec
  | "kissat_clear_marks", [.bits 64, .bits 64], [] => kissatClearMarksSpec
  | "kissat_analyze", [.bits 64, .bits 64], [.bits 64] => kissatAnalyzeSpec
  | "kissat_decide", [.bits 64], [.bits 64] => kissatDecideSpec
  | "kissat_solve_bytes", [.bits 64, .bits 64, .bits 64, .bits 64, .bits 64], [.bits 64] =>
      mainSpec
  | name, as, rs => dimacsExactEnv name as rs

theorem mkKissatEnv_sound
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hweaken : ∀ args m Q X, mainSpec args m Q X → kissatSolveBytesCoreSpec args m Q X) :
    ∀ f ∈ kissatFns, ∀ args m Q X,
      mkKissatEnv mainSpec f.name f.as f.rs args m Q X →
      Func.wp (mkKissatEnv mainSpec) f.body args m Q X := by
  intro f hf args m Q X hspec
  simp only [kissatFns, List.mem_append] at hf
  rcases hf with hd | hs
  · simp only [dimacs_fns, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact kissat_is_ws_wp _ args m Q X hspec
    · exact kissat_is_digit_wp _ args m Q X hspec
    · exact kissat_skip_ws_comments_wp _ (fun _ _ _ _ h => h) args m Q X hspec
    · exact kissat_skip_ws1_wp _ (fun _ _ _ _ h => h) args m Q X hspec
    · exact kissat_read_nat_wp _ (fun _ _ _ _ h => h) (fun _ _ _ _ h => h) args m Q X hspec
    · exact kissat_parse_header_wp _ (fun _ _ _ _ h => h) (fun _ _ _ _ h => h)
        (fun _ _ _ _ h => h) args m Q X hspec
    · exact kissat_next_lit_wp _ (fun _ _ _ _ h => h) (fun _ _ _ _ h => h) args m Q X hspec
    · exact kissat_check_model_exact_wp _ (fun _ _ _ _ h => h) (fun _ _ _ _ h => h)
        (fun _ _ _ _ h => h) args m Q X hspec
  · simp only [solver_fns, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    · exact kissat_assign_wp _ args m Q X hspec
    · exact kissat_add_watch_wp _ args m Q X hspec
    · exact kissat_add_clause_wp _ (fun _ _ _ _ h => h) args m Q X hspec
    · exact kissat_backtrack_wp _ args m Q X hspec
    · exact kissat_zero_tables_wp _ args m Q X hspec
    · exact kissat_init_state_wp _ (fun _ _ _ _ h => h) (fun _ _ _ _ h => h) args m Q X hspec
    · exact kissat_skip_clause_syntax_wp _ (fun _ _ _ _ h => h) args m Q X hspec
    · exact kissat_ingest_clause_wp _ (fun _ _ _ _ h => h) (fun _ _ _ _ h => h)
        (fun _ _ _ _ h => h) args m Q X hspec
    · exact kissat_parse_body_wp _ (fun _ _ _ _ h => h) (fun _ _ _ _ h => h)
        (fun _ _ _ _ h => h) args m Q X hspec
    · exact kissat_find_repl_wp _ args m Q X hspec
    · exact kissat_propagate_lit_wp _ (fun _ _ _ _ h => h) (fun _ _ _ _ h => h) args m Q X hspec
    · exact kissat_propagate_wp _ (fun _ _ _ _ h => h) args m Q X hspec
    · exact kissat_analyze_clause_wp _ args m Q X hspec
    · exact kissat_clear_marks_wp _ args m Q X hspec
    · exact kissat_analyze_wp _ (fun _ _ _ _ h => h) (fun _ _ _ _ h => h)
        (fun _ _ _ _ h => h) (fun _ _ _ _ h => h) (fun _ _ _ _ h => h) args m Q X hspec
    · exact kissat_decide_wp _ (fun _ _ _ _ h => h) args m Q X hspec
    · exact kissat_solve_bytes_core_wp _ (fun _ _ _ _ h => h) (fun _ _ _ _ h => h)
        (fun _ _ _ _ h => h) (fun _ _ _ _ h => h) (fun _ _ _ _ h => h) (fun _ _ _ _ h => h)
        args m Q X (hweaken args m Q X hspec)

theorem mkKissatEnv_noExit
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hnoex : ∀ args m Q X X', mainSpec args m Q X → mainSpec args m Q X') :
    ∀ g ∈ kissatFns, ∀ args m Q X X',
      mkKissatEnv mainSpec g.name g.as g.rs args m Q X →
      mkKissatEnv mainSpec g.name g.as g.rs args m Q X' := by
  intro g hg args m Q X X' h
  simp only [kissatFns, List.mem_append] at hg
  rcases hg with hd | hs
  · simp only [dimacs_fns, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact h
  · simp only [solver_fns, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    all_goals first | exact h | exact hnoex args m Q X X' h

theorem mkKissatEnv_moduleOk
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hweaken : ∀ args m Q X, mainSpec args m Q X → kissatSolveBytesCoreSpec args m Q X) :
    ModuleOk (mkKissatEnv mainSpec) kissatModule :=
  Module.moduleOk_of_checkAcyclic kissatModule_checkAcyclic kissatFns_wf
    (mkKissatEnv_sound mainSpec hweaken)

/-- Headline 25-function specification environment for `kissatModule`. -/
def kissatEnv : Env := mkKissatEnv kissatSolveBytesSpec

theorem kissatEnv_sound :
    ∀ f ∈ kissatFns, ∀ args m Q X,
      kissatEnv f.name f.as f.rs args m Q X →
      Func.wp kissatEnv f.body args m Q X :=
  mkKissatEnv_sound kissatSolveBytesSpec (fun _ _ _ _ => kissatSolveBytesCoreSpec_of_spec)

theorem kissatEnv_noExit :
    ∀ g ∈ kissatFns, ∀ args m Q X X',
      kissatEnv g.name g.as g.rs args m Q X →
      kissatEnv g.name g.as g.rs args m Q X' :=
  mkKissatEnv_noExit kissatSolveBytesSpec (fun _ _ _ _ _ h => h)

theorem kissatEnv_moduleOk : ModuleOk kissatEnv kissatModule :=
  mkKissatEnv_moduleOk kissatSolveBytesSpec (fun _ _ _ _ => kissatSolveBytesCoreSpec_of_spec)

/-- Headline source-level correctness of `kissat_solve_bytes` under `kissatEnv`:
returns `r ∈ {0, 10, 20}`, keeps `[cnf_ptr, cnf_ptr + cnf_len)` read-only, restores
`region work_ptr work_len`, and certifies UNSAT (`20`) and SAT (`10`). -/
theorem kissat_solve_bytes_correct
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} {X : XPost}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp kissatEnv kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α) ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m') X :=
  kissat_solve_bytes_wp kissatEnv
    (fun _ _ _ _ h => h) (fun _ _ _ _ h => h) (fun _ _ _ _ h => h)
    (fun _ _ _ _ h => h) (fun _ _ _ _ h => h) (fun _ _ _ _ h => h) _ m _ X
    ⟨cnfBytes, wlen, R, rfl, rfl, hcfit, hwfit, hm,
      fun _ _ hdom hu hs hm' => ⟨hdom, hu, hs, hm'⟩⟩

/-! ## 4. Concrete UNSAT (`20#64`) and SAT (`10#64`) non-vacuity witnesses -/

/-- Concrete UNSAT DIMACS input (`p cnf 1 2\n1 0\n-1 0\n`, 19 bytes). -/
def nvUnsatBytes : List UInt8 :=
  [112, 32, 99, 110, 102, 32, 49, 32, 50, 10, 49, 32, 48, 10, 45, 49, 32, 48, 10]

/-- Parsed `Std.Sat.CNF Nat` for `nvUnsatBytes`. -/
def nvUnsatCnf : CNF Nat :=
  (CNF.empty.add (CNF.Clause.ofLiterals [(1, true)])).add (CNF.Clause.ofLiterals [(1, false)])

theorem parseDimacs_nvUnsatBytes : parseDimacs nvUnsatBytes = some nvUnsatCnf :=
  rfl

/-- Concrete SAT DIMACS input (`p cnf 1 1\n1 0\n`, 14 bytes). -/
def nvSatBytes : List UInt8 :=
  [112, 32, 99, 110, 102, 32, 49, 32, 49, 10, 49, 32, 48, 10]

/-- Parsed `Std.Sat.CNF Nat` for `nvSatBytes`. -/
def nvSatCnf : CNF Nat :=
  CNF.empty.add (CNF.Clause.ofLiterals [(1, true)])

theorem parseDimacs_nvSatBytes : parseDimacs nvSatBytes = some nvSatCnf :=
  rfl

private theorem nvUnsat_header :
    parseHeader nvUnsatBytes = some (1, 2, nvUnsatBytes.drop 9) := by
  decide

private theorem nvUnsat_trace :
    UnitUnsatTrace 1 (List.replicate 2 0#8) (nvUnsatBytes.drop 9) 2 := by
  have hcl1 : parseClause 1 (nvUnsatBytes.drop 9) =
      some (CNF.Clause.ofLiterals [kissatLitToDimacsLiteral 0], nvUnsatBytes.drop 13) := rfl
  have hcl2 : parseClause 1 (nvUnsatBytes.drop 13) =
      some (CNF.Clause.ofLiterals [kissatLitToDimacsLiteral 1], [10]) := rfl
  have hrest : ∃ cnf, parseClauses 1 0 CNF.empty [10] = some cnf := ⟨CNF.empty, rfl⟩
  exact UnitUnsatTrace.step (l := 0) (by decide) hcl1 (by decide)
    (UnitUnsatTrace.conflict (l := 1) (by decide) hcl2 (by decide) hrest)

private theorem nvSat_header :
    parseHeader nvSatBytes = some (1, 1, nvSatBytes.drop 9) := by
  decide

private theorem nvSat_trace :
    UnitSatTrace 1 (List.replicate 2 0#8) 0 (nvSatBytes.drop 9) 1 [1#8, 0xFF#8] 1 := by
  have hcl1 : parseClause 1 (nvSatBytes.drop 9) =
      some (CNF.Clause.ofLiterals [kissatLitToDimacsLiteral 0], [10]) := rfl
  have hdone : UnitSatTrace 1 [1#8, 0xFF#8] 1 [10] 0 [1#8, 0xFF#8] 1 :=
    UnitSatTrace.done (by decide)
  exact UnitSatTrace.step (l := 0) (by decide) hcl1 (by decide) (by simpa using hdone)

private theorem nvSat_checkModel :
    runKissatCheckModel nvSatBytes ([1#8, 0xFF#8].map UInt8.ofBitVec) 1 = true := by
  decide

/-- Concrete UNSAT witness contract for `kissat_solve_bytes` (`nvUnsatBytes`, `work_len = 512`,
`fuel = 16`): unconditionally returns `20#64` and proves `nvUnsatCnf.Unsat`. -/
def kissatSolveBytesUnsatWitnessSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
  fun (cnf_ptr, cnf_len, work_ptr, work_len, fuel, ()) m Q _ =>
    ∃ R : Mem 64 → Prop,
      cnf_len = BitVec.ofNat 64 nvUnsatBytes.length ∧
      work_len = 512#64 ∧
      fuel = 16#64 ∧
      cnf_ptr.toNat + nvUnsatBytes.length < 2 ^ 64 ∧
      work_ptr.toNat + 512 < 2 ^ 64 ∧
      (bytes cnf_ptr nvUnsatBytes ⋆ region work_ptr 512 ⋆ R) m ∧
      ∀ m', nvUnsatCnf.Unsat →
        (bytes cnf_ptr nvUnsatBytes ⋆ region work_ptr 512 ⋆ R) m' →
        Q (20#64, ()) m'

theorem kissatSolveBytesCoreSpec_of_unsatWitness
    {args : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : kissatSolveBytesUnsatWitnessSpec args m Q X) :
    kissatSolveBytesCoreSpec args m Q X := by
  obtain ⟨R, hcl, hwl, hfu, hcfit, hwfit, hm, hQ⟩ := h
  refine ⟨nvUnsatBytes, 512, R, hcl, hwl, hcfit, hwfit, hm,
    fun r m' _ hu _ huns_w _ hm' => ?_⟩
  have hr20 : r = 20#64 :=
    huns_w 1 2 9 (by rw [hfu]; decide)
      (by unfold fixedBytes valsBytes markBytes u32VarBytes whBytes; decide)
      (by decide) nvUnsat_header nvUnsat_trace
  subst hr20
  obtain ⟨cnf, hparse, huns⟩ := hu rfl
  rw [parseDimacs_nvUnsatBytes] at hparse
  cases Option.some.inj hparse
  exact hQ m' huns hm'

/-- Closed 25-function environment for concrete UNSAT non-vacuity (`20#64`). -/
def kissatUnsatWitnessEnv : Env := mkKissatEnv kissatSolveBytesUnsatWitnessSpec

theorem kissatUnsatWitnessEnv_sound :
    ∀ f ∈ kissatFns, ∀ args m Q X,
      kissatUnsatWitnessEnv f.name f.as f.rs args m Q X →
      Func.wp kissatUnsatWitnessEnv f.body args m Q X :=
  mkKissatEnv_sound kissatSolveBytesUnsatWitnessSpec
    (fun _ _ _ _ => kissatSolveBytesCoreSpec_of_unsatWitness)

theorem kissatUnsatWitnessEnv_noExit :
    ∀ g ∈ kissatFns, ∀ args m Q X X',
      kissatUnsatWitnessEnv g.name g.as g.rs args m Q X →
      kissatUnsatWitnessEnv g.name g.as g.rs args m Q X' :=
  mkKissatEnv_noExit kissatSolveBytesUnsatWitnessSpec (fun _ _ _ _ _ h => h)

theorem kissatUnsatWitnessEnv_moduleOk : ModuleOk kissatUnsatWitnessEnv kissatModule :=
  mkKissatEnv_moduleOk kissatSolveBytesUnsatWitnessSpec
    (fun _ _ _ _ => kissatSolveBytesCoreSpec_of_unsatWitness)

/-- Concrete SAT witness contract for `kissat_solve_bytes` (`nvSatBytes`, `work_len = 512`,
`fuel = 16`): unconditionally returns `10#64` and proves
`¬ nvSatCnf.Unsat ∧ ∃ α, nvSatCnf.Sat α`. -/
def kissatSolveBytesSatWitnessSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
  fun (cnf_ptr, cnf_len, work_ptr, work_len, fuel, ()) m Q _ =>
    ∃ R : Mem 64 → Prop,
      cnf_len = BitVec.ofNat 64 nvSatBytes.length ∧
      work_len = 512#64 ∧
      fuel = 16#64 ∧
      cnf_ptr.toNat + nvSatBytes.length < 2 ^ 64 ∧
      work_ptr.toNat + 512 < 2 ^ 64 ∧
      (bytes cnf_ptr nvSatBytes ⋆ region work_ptr 512 ⋆ R) m ∧
      ∀ m', ¬ nvSatCnf.Unsat → (∃ α, nvSatCnf.Sat α) →
        (bytes cnf_ptr nvSatBytes ⋆ region work_ptr 512 ⋆ R) m' →
        Q (10#64, ()) m'

theorem kissatSolveBytesCoreSpec_of_satWitness
    {args : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : kissatSolveBytesSatWitnessSpec args m Q X) :
    kissatSolveBytesCoreSpec args m Q X := by
  obtain ⟨R, hcl, hwl, hfu, hcfit, hwfit, hm, hQ⟩ := h
  refine ⟨nvSatBytes, 512, R, hcl, hwl, hcfit, hwfit, hm,
    fun r m' _ _ hs _ hsat_w hm' => ?_⟩
  have hr10 : r = 10#64 :=
    hsat_w 1 1 9 [1#8, 0xFF#8] 1 (by rw [hfu]; decide)
      (by unfold fixedBytes valsBytes markBytes u32VarBytes whBytes; decide)
      (by decide) nvSat_header nvSat_trace
      (fun v hv => by rw [show v = 0 by omega]; decide)
      nvSat_checkModel
  subst hr10
  obtain ⟨cnf, hparse, hnu, hsat⟩ := hs rfl
  rw [parseDimacs_nvSatBytes] at hparse
  cases Option.some.inj hparse
  exact hQ m' hnu hsat hm'

/-- Closed 25-function environment for concrete SAT non-vacuity (`10#64`). -/
def kissatSatWitnessEnv : Env := mkKissatEnv kissatSolveBytesSatWitnessSpec

theorem kissatSatWitnessEnv_sound :
    ∀ f ∈ kissatFns, ∀ args m Q X,
      kissatSatWitnessEnv f.name f.as f.rs args m Q X →
      Func.wp kissatSatWitnessEnv f.body args m Q X :=
  mkKissatEnv_sound kissatSolveBytesSatWitnessSpec
    (fun _ _ _ _ => kissatSolveBytesCoreSpec_of_satWitness)

theorem kissatSatWitnessEnv_noExit :
    ∀ g ∈ kissatFns, ∀ args m Q X X',
      kissatSatWitnessEnv g.name g.as g.rs args m Q X →
      kissatSatWitnessEnv g.name g.as g.rs args m Q X' :=
  mkKissatEnv_noExit kissatSolveBytesSatWitnessSpec (fun _ _ _ _ _ h => h)

theorem kissatSatWitnessEnv_moduleOk : ModuleOk kissatSatWitnessEnv kissatModule :=
  mkKissatEnv_moduleOk kissatSolveBytesSatWitnessSpec
    (fun _ _ _ _ => kissatSolveBytesCoreSpec_of_satWitness)

/-! ## 5. Concrete memory payload helpers for `{Amd64,Arm64}.Kissat` non-vacuity -/

abbrev kissatNvCnfPtr : BitVec 64 := 0x1000#64
abbrev kissatNvWorkPtr (cnfBytes : List UInt8) : BitVec 64 :=
  kissatNvCnfPtr + BitVec.ofNat 64 cnfBytes.length

def kissatPayload (cnfBytes : List UInt8) : List UInt8 :=
  cnfBytes ++ List.replicate 512 0

theorem kissatPayload_length (cnfBytes : List UInt8) :
    (kissatPayload cnfBytes).length = cnfBytes.length + 512 := by
  simp only [kissatPayload, List.length_append, List.length_replicate]

theorem kissatPayload_sep (cnfBytes : List UInt8) (hcb : cnfBytes.length ≤ 4096) :
    (bytes kissatNvCnfPtr cnfBytes ⋆ region (kissatNvWorkPtr cnfBytes) 512)
      ((kissatPayload cnfBytes).At kissatNvCnfPtr) := by
  have h512 : (List.replicate 512 (0 : UInt8)).length = 512 := List.length_replicate
  have h1 := Mem.At_append_sep cnfBytes (List.replicate 512 0) kissatNvCnfPtr
    (by simp only [h512]; omega)
  have h0 : (Eq ((cnfBytes ++ List.replicate 512 0).At kissatNvCnfPtr))
      ((kissatPayload cnfBytes).At kissatNvCnfPtr) := rfl
  rw [h1] at h0
  exact sep_mono_r (fun _ hfW => ⟨List.replicate 512 0, h512, hfW.symm⟩) h0

/-- Source-level concrete UNSAT non-vacuity: `kissat_solve_bytes` returns `20#64` and proves
`nvUnsatCnf.Unsat` on `nvUnsatBytes` with `work_len = 512` and `fuel = 16`. -/
theorem kissat_unsat_nonvacuous :
    let m0 : Mem 64 := (kissatPayload nvUnsatBytes).At kissatNvCnfPtr
    Func.wp kissatUnsatWitnessEnv kissat_solve_bytes_body
      (kissatNvCnfPtr, BitVec.ofNat 64 nvUnsatBytes.length,
        kissatNvWorkPtr nvUnsatBytes, 512#64, 16#64, ()) m0
      (fun rs _ => rs = (20#64, ()) ∧ nvUnsatCnf.Unsat) (fun _ _ _ _ => False) := by
  apply kissatUnsatWitnessEnv_sound (f := kissat_solve_bytes) (by simp [kissatFns, solver_fns])
  exact ⟨emp, rfl, rfl, rfl, by decide, by decide,
    by rw [sep_emp]; exact kissatPayload_sep nvUnsatBytes (by decide),
    fun _ hu _ => ⟨rfl, hu⟩⟩

/-- Source-level concrete SAT non-vacuity: `kissat_solve_bytes` returns `10#64` and proves
`¬ nvSatCnf.Unsat ∧ ∃ α, nvSatCnf.Sat α` on `nvSatBytes` with `work_len = 512` and `fuel = 16`. -/
theorem kissat_sat_nonvacuous :
    let m0 : Mem 64 := (kissatPayload nvSatBytes).At kissatNvCnfPtr
    Func.wp kissatSatWitnessEnv kissat_solve_bytes_body
      (kissatNvCnfPtr, BitVec.ofNat 64 nvSatBytes.length,
        kissatNvWorkPtr nvSatBytes, 512#64, 16#64, ()) m0
      (fun rs _ => rs = (10#64, ()) ∧ ¬ nvSatCnf.Unsat ∧ ∃ α, nvSatCnf.Sat α)
      (fun _ _ _ _ => False) := by
  apply kissatSatWitnessEnv_sound (f := kissat_solve_bytes) (by simp [kissatFns, solver_fns])
  exact ⟨emp, rfl, rfl, rfl, by decide, by decide,
    by rw [sep_emp]; exact kissatPayload_sep nvSatBytes (by decide),
    fun _ hnu hsat _ => ⟨rfl, hnu, hsat⟩⟩

end LeanQbe.T.Examples.Kissat
