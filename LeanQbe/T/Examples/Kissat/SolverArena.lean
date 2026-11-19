module

public import LeanQbe.T.Examples.Kissat.Solver
public import LeanQbe.T.Examples.Kissat.DimacsLemmas
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat C0 Arena Layout, `BitVec` Helpers, and Semantic Bridges (`X1` Stage B2)

Defines:
1. 1-based to 0-based CNF shift (`shiftDownCnf`), propositional entailment/resolution bridges,
   and `List.Nodup` pigeonhole bounds.
2. Typed-array / `region` conversions (`array_to_region`, `region_to_array_i8`,
   `region_to_array_i32`, `bytesOf_i8_eq_map`, `array_slice_focus`) and `BitVec` address lemmas.
3. `ArenaCfg`, `ArenaState`, `ArenaMem`, `ArenaInv`, `ArenaRest`, collapse back to
   `region c.hdr c.avail`, and direct load/store accessors on `(ArenaMem c s ⋆ R) m`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open Kraken.Bedrock2.Test

/-! ## 1. `shiftDownCnf`, semantic entailment bridges, and pigeonhole bounds -/

/-- Shift a 1-based DIMACS clause (`v ≥ 1`) down to 0-based Kissat variables (`v ↦ v - 1`). -/
def shiftDownClause (cl : CNF.Clause Nat) : CNF.Clause Nat :=
  CNF.Clause.ofLiterals (cl.literals.map fun (v, p) => (v - 1, p))

/-- Shift a 1-based DIMACS `CNF Nat` down to 0-based Kissat variables. -/
def shiftDownCnf (cnf : CNF Nat) : CNF Nat :=
  ⟨cnf.clauses.map shiftDownClause⟩

/-- Every variable occurring in `cnf` is positive (`1`-based DIMACS convention). -/
def CnfVarsPos (cnf : CNF Nat) : Prop :=
  ∀ cl ∈ cnf, ∀ lit ∈ cl.literals, 1 ≤ lit.1

theorem cnfVarsPos_empty : CnfVarsPos (CNF.empty : CNF Nat) := by
  intro cl hcl
  simp [CNF.empty, CNF.Internal.mem_iff] at hcl

theorem cnfVarsPos_add {cnf : CNF Nat} {cl : CNF.Clause Nat}
    (h1 : CnfVarsPos cnf) (h2 : ∀ lit ∈ cl.literals, 1 ≤ lit.1) :
    CnfVarsPos (cnf.add cl) := by
  intro c hc
  rcases CNF.mem_add.mp hc with rfl | hc'
  · exact h2
  · exact h1 c hc'

theorem shiftDownClause_sat_of_sat {cl : CNF.Clause Nat} {α : Nat → Bool}
    (hpos : ∀ lit ∈ cl.literals, 1 ≤ lit.1) (hsat : cl.Sat α) :
    (shiftDownClause cl).Sat (fun v => α (v + 1)) := by
  rw [CNF.Clause.sat_iff_exists_mem_eq] at hsat ⊢
  obtain ⟨⟨v, p⟩, hmem, heq⟩ := hsat
  have hmem' : (v, p) ∈ cl.literals := CNF.Clause.mem_literals_iff.mpr hmem
  have hv1 : 1 ≤ v := hpos (v, p) hmem'
  refine ⟨(v - 1, p), ?_, ?_⟩
  · rw [← CNF.Clause.mem_literals_iff, shiftDownClause, CNF.Clause.literals_ofLiterals]
    exact List.mem_map.mpr ⟨(v, p), hmem', rfl⟩
  · simpa [Nat.sub_add_cancel hv1] using heq

theorem shiftDownCnf_unsat {cnf : CNF Nat} (hpos : CnfVarsPos cnf)
    (hu : (shiftDownCnf cnf).Unsat) : cnf.Unsat := by
  rw [CNF.unsat_iff_not_sat] at hu ⊢
  intro α hα
  apply hu (fun v => α (v + 1))
  rw [CNF.sat_iff_all_mem_sat] at hα ⊢
  intro cl' hcl'
  rw [CNF.Internal.mem_iff, shiftDownCnf, Array.mem_map] at hcl'
  obtain ⟨cl, hcl, rfl⟩ := hcl'
  have hmem : cl ∈ cnf := CNF.Internal.mem_iff.mpr hcl
  exact shiftDownClause_sat_of_sat (hpos cl hmem) (hα cl hmem)

theorem shiftDownCnf_add (cnf : CNF Nat) (cl : CNF.Clause Nat) :
    shiftDownCnf (cnf.add cl) = (shiftDownCnf cnf).add (shiftDownClause cl) := by
  simp [shiftDownCnf, CNF.add]

theorem shiftDownCnf_entails_add (cnf : CNF Nat) (cl : CNF.Clause Nat) :
    (shiftDownCnf (cnf.add cl)).Entails (shiftDownCnf cnf) := by
  rw [shiftDownCnf_add, CNF.entails_def]
  intro α hα
  exact (CNF.sat_add.mp hα).2

theorem shiftDownCnf_entails_added (cnf : CNF Nat) (cl : CNF.Clause Nat) :
    (shiftDownCnf (cnf.add cl)).EntailsClause (shiftDownClause cl) := by
  rw [shiftDownCnf_add, CNF.entails_clause_def]
  intro α hα
  exact (CNF.sat_add.mp hα).1

theorem shiftDownClause_kissatLits (lits : List Nat) :
    shiftDownClause (CNF.Clause.ofLiterals (lits.map kissatLitToDimacsLiteral)) =
      cnfClause lits := by
  apply CNF.Clause.ext
  simp [shiftDownClause, cnfClause, kissatLitToDimacsLiteral, litToLiteral, Function.comp_def]

theorem entails_of_mem_or_false {F0 : CNF Nat} {c1 c2 : List Nat}
    (h1 : F0.EntailsClause (cnfClause c1))
    (hsub : ∀ l ∈ c1, l ∈ c2 ∨ F0.EntailsClause (cnfClause [litNeg l])) :
    F0.EntailsClause (cnfClause c2) := by
  rw [CNF.entails_clause_def] at h1 ⊢
  intro α hα
  obtain ⟨l, hl, hsat⟩ := (clause_sat_cnfClause_iff α c1).mp (h1 α hα)
  rcases hsub l hl with hin | hfalse
  · exact (clause_sat_cnfClause_iff α c2).mpr ⟨l, hin, hsat⟩
  · have hneg := CNF.entails_clause_def.mp hfalse α hα
    exact absurd ((sat_cnfClause_singleton α l).mpr hsat) ((sat_cnfClause_litNeg_iff α l).mp hneg)

theorem entails_resolve_to {F0 : CNF Nat} {p : Nat} {c1 c2 c3 : List Nat}
    (h1 : F0.EntailsClause (cnfClause c1))
    (h2 : F0.EntailsClause (cnfClause c2))
    (hs1 : ∀ l ∈ c1, l = p ∨ l ∈ c3 ∨ F0.EntailsClause (cnfClause [litNeg l]))
    (hs2 : ∀ l ∈ c2, l = litNeg p ∨ l ∈ c3 ∨ F0.EntailsClause (cnfClause [litNeg l])) :
    F0.EntailsClause (cnfClause c3) := by
  refine entails_of_mem_or_false (entails_resolve (p := p) h1 h2) fun l hl => ?_
  unfold resolveOn at hl
  rcases List.mem_append.mp hl with hl1 | hl2
  · rw [List.mem_filter, bne_iff_ne] at hl1
    rcases hs1 l hl1.1 with rfl | hin | hf
    · exact absurd rfl hl1.2
    · exact Or.inl hin
    · exact Or.inr hf
  · rw [List.mem_filter, bne_iff_ne] at hl2
    rcases hs2 l hl2.1 with rfl | hin | hf
    · exact absurd rfl hl2.2
    · exact Or.inl hin
    · exact Or.inr hf

theorem nodup_map_of_inj {α β : Type} {f : α → β} :
    ∀ {xs : List α}, xs.Nodup → (∀ a ∈ xs, ∀ b ∈ xs, f a = f b → a = b) → (xs.map f).Nodup
  | [], _, _ => by simp
  | x :: xs, hnd, hinj => by
    rw [List.nodup_cons] at hnd
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hmem => ?_, nodup_map_of_inj hnd.2 fun a ha b hb =>
      hinj a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)⟩
    obtain ⟨y, hy, heq⟩ := List.mem_map.mp hmem
    have hxy := hinj y (List.mem_cons_of_mem _ hy) x List.mem_cons_self heq
    exact hnd.1 (hxy ▸ hy)

/-- Pigeonhole bound for `List.Nodup` elements in `0 ..< n`. -/
theorem nodup_length_le_of_lt :
    ∀ (n : Nat) (xs : List Nat), xs.Nodup → (∀ x ∈ xs, x < n) → xs.length ≤ n
  | 0, xs, _, hlt => by
    cases xs with
    | nil => simp
    | cons x _ => have := hlt x (by simp); omega
  | n + 1, xs, hnd, hlt => by
    have hnd' : (xs.erase n).Nodup := hnd.erase n
    have hlt' : ∀ y ∈ xs.erase n, y < n := by
      intro y hy
      have hne : y ≠ n := by
        intro heq; subst heq
        exact (List.Nodup.not_mem_erase hnd) hy
      have hyx : y ∈ xs := List.mem_of_mem_erase hy
      have := hlt y hyx; omega
    have hle := nodup_length_le_of_lt n (xs.erase n) hnd' hlt'
    have hlen : xs.length ≤ (xs.erase n).length + 1 := by
      by_cases hmem : n ∈ xs
      · rw [List.length_erase_of_mem hmem]; have := List.length_pos_of_mem hmem; omega
      · rw [List.erase_of_not_mem hmem]; omega
    omega

theorem nodup_lt_of_missing {n v : Nat} {xs : List Nat}
    (hnd : xs.Nodup) (hlt : ∀ x ∈ xs, x < n) (hv : v < n) (hnot : v ∉ xs) :
    xs.length < n := by
  have h := nodup_length_le_of_lt n (v :: xs) (List.nodup_cons.mpr ⟨hnot, hnd⟩)
    (fun x hx => (List.mem_cons.mp hx).elim (fun h => h ▸ hv) (hlt x))
  simp only [List.length_cons] at h
  omega

/-- Injection from `{0..k-1}` into `{0..n-1}` missing a point `v < n` forces `k < n`. -/
theorem inj_lt_of_missing {k n v : Nat} (f : Nat → Nat)
    (hinj : ∀ i j, i < k → j < k → f i = f j → i = j)
    (hlt : ∀ i < k, f i < n) (hv : v < n) (hmiss : ∀ i < k, f i ≠ v) : k < n := by
  let xs := (List.range k).map f
  have hlen : xs.length = k := by simp [xs]
  have hnd : xs.Nodup :=
    nodup_map_of_inj List.nodup_range fun i hi j hj heq =>
      hinj i j (List.mem_range.mp hi) (List.mem_range.mp hj) heq
  have hmem : ∀ x ∈ xs, x < n := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact hlt i (List.mem_range.mp hi)
  have hnot : v ∉ xs := by
    intro hx
    obtain ⟨i, hi, heq⟩ := List.mem_map.mp hx
    exact hmiss i (List.mem_range.mp hi) heq
  rw [← hlen]
  exact nodup_lt_of_missing hnd hmem hv hnot

/-- Surjection from `{0..k-1}` onto `{1..L}` implies `L ≤ k`. -/
theorem le_of_surj_range1 {L k : Nat} (g : Nat → Nat)
    (hsurj : ∀ x, 1 ≤ x → x ≤ L → ∃ i < k, g i = x) : L ≤ k := by
  let ys := (List.range L).map (fun x => x + 1)
  have hsub : ∀ y ∈ ys, ∃ i < k, g i = y := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    have hxlt := List.mem_range.mp hx
    exact hsurj (x + 1) (by omega) (by omega)
  have hnd : ys.Nodup := nodup_map_of_inj List.nodup_range fun a _ b _ h => by omega
  have hlen := nodup_length_le_of_lt k
    (ys.map fun y => (List.range k).findIdx (fun i => g i == y))
    (nodup_map_of_inj hnd fun a ha b hb heq => by
      obtain ⟨ia, hia, hga⟩ := hsub a ha
      obtain ⟨ib, hib, hgb⟩ := hsub b hb
      have hfa : (List.range k).findIdx (fun i => g i == a) < (List.range k).length :=
        List.findIdx_lt_length.mpr ⟨ia, List.mem_range.mpr hia, by simp [hga]⟩
      have hfb : (List.range k).findIdx (fun i => g i == b) < (List.range k).length :=
        List.findIdx_lt_length.mpr ⟨ib, List.mem_range.mpr hib, by simp [hgb]⟩
      have hpa := List.findIdx_getElem (xs := List.range k) (p := fun i => g i == a) (w := hfa)
      have hpb := List.findIdx_getElem (xs := List.range k) (p := fun i => g i == b) (w := hfb)
      simp only [List.getElem_range, beq_iff_eq] at hpa hpb
      rw [heq] at hpa
      exact hpa.symm.trans hpb)
    (by
      intro idx hidx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hidx
      obtain ⟨i, hi, hgi⟩ := hsub y hy
      have hlt : (List.range k).findIdx (fun j => g j == y) < (List.range k).length :=
        List.findIdx_lt_length.mpr ⟨i, List.mem_range.mpr hi, by simp [hgi]⟩
      rwa [List.length_range] at hlt)
  simpa [ys] using hlen

/-! ## 2. Typed-array / `region` conversions and `BitVec` address helpers -/

theorem array_to_region {t : Ty} {a : BitVec 64} {xs : List (Val t)} {f : Mem 64}
    (h : t.bytes * xs.length ≤ 2 ^ 64) (hf : array a xs f) :
    region a (t.bytes * xs.length) f :=
  ⟨bytesOf xs, bytesOf_length xs, array_eq_bytesOf a xs h hf⟩

theorem bytesOf_i8_eq_map (xs : List (BitVec 8)) :
    bytesOf (t := i8) xs = xs.map UInt8.ofBitVec := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [bytesOf, List.flatMap_cons, List.map_cons, toBits, i8, Ty.bytes, Ty.size] at ih ⊢
    rw [ih]
    have h1 : Int.toBytes 1 (x.setWidth 8).toInt = [UInt8.ofBitVec x] := by
      rw [BitVec.setWidth_eq, ← Int.toBytes_emod, show (8 * 1 : Nat) = 8 by rfl]
      change Int.toBytes 1 (x.toInt % (2 ^ 8 : Int)) = [UInt8.ofBitVec x]
      rw [BitVec.toInt_emod_two_pow]
      exact toBytes_u8 (UInt8.ofBitVec x)
    rw [h1]; rfl

theorem byte1_eq_cell_i8 (a v : BitVec 64) : byte1 a v = cell (t := i8) a (v.setWidth 8) := by
  unfold byte1 cell; congr 2
  have h1 : (8 * i8.bytes : Nat) = 8 := rfl
  rw [← Int.toBytes_emod (n := 1), ← Int.toBytes_emod (n := i8.bytes)]
  congr 1
  simp only [Int.take, toBits, i8, Ty.bytes, Ty.size, BitVec.setWidth_eq]
  change (v.toNat : Int) % (2 ^ 8 : Int) = (v.setWidth 8).toInt % (2 ^ 8 : Int)
  rw [BitVec.toInt_emod_two_pow, BitVec.toNat_setWidth]
  exact_mod_cast (rfl : v.toNat % 2 ^ 8 = v.toNat % 2 ^ 8)

theorem int4_eq_cell_i32 (a v : BitVec 64) : int4 a v = cell (t := i32) a (v.setWidth 32) := by
  unfold int4 cell; congr 2
  rw [← Int.toBytes_emod (n := 4), ← Int.toBytes_emod (n := i32.bytes)]
  congr 1
  simp only [Int.take, toBits, i32, Ty.bytes, Ty.size, BitVec.setWidth_eq]
  change (v.toNat : Int) % (2 ^ 32 : Int) = (v.setWidth 32).toInt % (2 ^ 32 : Int)
  rw [BitVec.toInt_emod_two_pow, BitVec.toNat_setWidth]
  exact_mod_cast (rfl : v.toNat % 2 ^ 32 = v.toNat % 2 ^ 32)

theorem byte1Array_eq_array_i8 (a : BitVec 64) (xs : List (BitVec 64)) :
    byte1Array a xs = array (t := i8) a (xs.map (·.setWidth 8)) := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    rw [byte1Array_cons, List.map_cons, array_cons, byte1_eq_cell_i8, ih]; rfl

theorem int4Array_eq_array_i32 (a : BitVec 64) (xs : List (BitVec 64)) :
    int4Array a xs = array (t := i32) a (xs.map (·.setWidth 32)) := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    rw [int4Array_cons, List.map_cons, array_cons, int4_eq_cell_i32, ih]; rfl

theorem region_to_array_i8 {a : BitVec 64} (k : Nat) (hk : k ≤ 2 ^ 64) {f : Mem 64}
    (hf : region a k f) : ∃ xs : List (BitVec 8), xs.length = k ∧ array (t := i8) a xs f := by
  obtain ⟨ws, hlen, hba⟩ := region_to_byte1Array k hk hf
  rw [byte1Array_eq_array_i8] at hba
  exact ⟨ws.map (·.setWidth 8), by simp [hlen], hba⟩

theorem region_to_array_i32 {a : BitVec 64} (k : Nat) (hk : 4 * k ≤ 2 ^ 64) {f : Mem 64}
    (hf : region a (4 * k) f) :
    ∃ xs : List (BitVec 32), xs.length = k ∧ array (t := i32) a xs f := by
  obtain ⟨ws, hlen, hia⟩ := region_to_int4Array k hk hf
  rw [int4Array_eq_array_i32] at hia
  exact ⟨ws.map (·.setWidth 32), by simp [hlen], hia⟩

theorem region_to_array64 {a : BitVec 64} (k : Nat) (hk : 8 * k ≤ 2 ^ 64) {f : Mem 64}
    (hf : region a (8 * k) f) : ∃ xs : List (BitVec 64), xs.length = k ∧ array64 a xs f := by
  obtain ⟨ws, hlen, hwa⟩ := region_to_word8Array k hk hf
  rw [← array64_eq_word8Array] at hwa
  exact ⟨ws, hlen, hwa⟩

theorem array_slice_focus {t : Ty} (a : BitVec 64) (xs : List (Val t)) {off sz : Nat}
    (h : off + sz ≤ xs.length) :
    array a xs =
      (array (a + BitVec.ofNat 64 (t.bytes * off)) ((xs.drop off).take sz) ⋆
        (array a (xs.take off) ⋆
          array (a + BitVec.ofNat 64 (t.bytes * (off + sz))) (xs.drop (off + sz)))) := by
  have h1 : xs = xs.take off ++ ((xs.drop off).take sz ++ xs.drop (off + sz)) := by
    have hd : xs.drop (off + sz) = (xs.drop off).drop sz := by
      rw [List.drop_drop, Nat.add_comm]
    rw [hd, List.take_append_drop, List.take_append_drop]
  have hlen1 : (xs.take off).length = off := List.length_take_of_le (by omega)
  have hlen2 : ((xs.drop off).take sz).length = sz := by
    rw [List.length_take, List.length_drop]; omega
  conv => lhs; rw [h1]
  rw [array_append, hlen1, array_append, hlen2, ptr_add_ofNat, ← Nat.mul_add]
  ac_rfl

/-- `BitVec` address and arithmetic helpers matching C0 lowering. -/
theorem bv32_zext64_eq (x : BitVec 32) : x.setWidth 64 = BitVec.ofNat 64 x.toNat := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ 64)]

theorem bv32_lshr_1 (x : BitVec 32) : (x >>> 1).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem bv32_xor_1 (x : BitVec 32) : (x ^^^ (1 : BitVec 32)).toNat = x.toNat ^^^ 1 := by
  simp [BitVec.toNat_xor]

theorem bv32_and_1 (x : BitVec 32) : (x &&& (1 : BitVec 32)).toNat = x.toNat % 2 := by
  simp [BitVec.toNat_and, Nat.and_one_is_mod]

theorem bv_ofNat_toNat_eq {n : Nat} (x : BitVec n) : BitVec.ofNat n x.toNat = x :=
  BitVec.eq_of_toNat_eq (by simp)

theorem litNeg_lt_two_mul {l mv : Nat} (hl : l < 2 * mv) : (l ^^^ 1) < 2 * mv := by
  have h := litNeg_eq l; unfold litNeg at h; split at h <;> omega

theorem bv32_mul4_eq (x : BitVec 32) :
    x.setWidth 64 * (4 : BitVec 64) = BitVec.ofNat 64 (4 * x.toNat) := by
  rw [bv32_zext64_eq]; grind

theorem bv64_mul4_nat (n : Nat) :
    BitVec.ofNat 64 n * (4 : BitVec 64) = BitVec.ofNat 64 (4 * n) := by grind

theorem bv32_mul16_eq (x : BitVec 32) :
    x.setWidth 64 * (16 : BitVec 64) = BitVec.ofNat 64 (4 * (4 * x.toNat)) := by
  rw [bv32_zext64_eq]; grind

theorem bv64_mul16_nat (n : Nat) :
    BitVec.ofNat 64 n * (16 : BitVec 64) = BitVec.ofNat 64 (4 * (4 * n)) := by grind

theorem bv_shl_sext1 {n : Nat} :
    BitVec.ofNat 64 n <<< (((1 : BitVec 32).signExtend 64).toNat % 64) =
      BitVec.ofNat 64 (2 * n) := by
  have hs : ((1 : BitVec 32).signExtend 64).toNat % 64 = 1 := rfl
  rw [hs]; apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega

theorem bv_shl_sext2 {n : Nat} :
    BitVec.ofNat 64 n <<< (((2 : BitVec 32).signExtend 64).toNat % 64) =
      BitVec.ofNat 64 (4 * n) := by
  have hs : ((2 : BitVec 32).signExtend 64).toNat % 64 = 2 := rfl
  rw [hs]; apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega

theorem bv_shl_sext4 {n : Nat} :
    BitVec.ofNat 64 n <<< (((4 : BitVec 32).signExtend 64).toNat % 64) =
      BitVec.ofNat 64 (16 * n) := by
  have hs : ((4 : BitVec 32).signExtend 64).toNat % 64 = 4 := rfl
  rw [hs]; apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega

theorem bv_shr_sext2 {n : Nat} (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n >>> (((2 : BitVec 32).signExtend 64).toNat % 64) =
      BitVec.ofNat 64 (n / 4) := by
  have hs : ((2 : BitVec 32).signExtend 64).toNat % 64 = 2 := rfl
  rw [hs]; apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (by omega : n / 4 < 2 ^ 64)]

theorem bv_shr_sext6 {n : Nat} (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n >>> (((6 : BitVec 32).signExtend 64).toNat % 64) =
      BitVec.ofNat 64 (n / 64) := by
  have hs : ((6 : BitVec 32).signExtend 64).toNat % 64 = 6 := rfl
  rw [hs]; apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (by omega : n / 64 < 2 ^ 64)]

theorem bv64_trunc32_ofNat {n : Nat} (hn : n < 2 ^ 32) :
    (BitVec.ofNat 64 n).setWidth 32 = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  simp [Nat.mod_eq_of_lt hn]

theorem bv32_ofNat_toNat {n : Nat} (hn : n < 2 ^ 32) :
    (BitVec.ofNat 32 n).toNat = n := by
  simp [Nat.mod_eq_of_lt hn]

theorem bv64_ofNat_toNat {n : Nat} (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n).toNat = n := by
  simp [Nat.mod_eq_of_lt hn]

theorem bv32_ult_eq {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (BitVec.ofNat 32 a).ult (BitVec.ofNat 32 b) = decide (a < b) := by
  simp [BitVec.ult, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem bv32_ule_eq {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (BitVec.ofNat 32 a).ule (BitVec.ofNat 32 b) = decide (a ≤ b) := by
  simp [BitVec.ule, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem trunc32_8_zero : (0 : BitVec 32).setWidth 8 = 0#8 := rfl
theorem trunc32_8_one : (1 : BitVec 32).setWidth 8 = 1#8 := rfl
theorem trunc32_8_neg1 : (-(1 : BitVec 32)).setWidth 8 = 0xFF#8 := rfl

theorem i8_sext32_zero : (0#8).signExtend 32 = 0#32 := rfl

theorem i8_vals_sgt0 {b : BitVec 8} (hd : b = 0#8 ∨ b = 1#8 ∨ b = 0xFF#8) :
    (0#32).slt (b.signExtend 32) = true ↔ b = 1#8 := by
  rcases hd with rfl | rfl | rfl <;> decide

theorem i8_vals_slt0 {b : BitVec 8} (hd : b = 0#8 ∨ b = 1#8 ∨ b = 0xFF#8) :
    (b.signExtend 32).slt 0#32 = true ↔ b = 0xFF#8 := by
  rcases hd with rfl | rfl | rfl <;> decide

theorem i8_vals_eq0 {b : BitVec 8} (hd : b = 0#8 ∨ b = 1#8 ∨ b = 0xFF#8) :
    b.signExtend 32 = 0#32 ↔ b = 0#8 := by
  rcases hd with rfl | rfl | rfl <;> decide

/-! ## 3. Arena geometry (`ArenaCfg`), state (`ArenaState`), and memory predicate (`ArenaMem`) -/

/-- Rounded 8-byte-aligned byte sizes matching `kissat_init_state`. -/
def valsBytes (mv : Nat) : Nat := ((2 * mv + 7) / 8) * 8
def markBytes (mv : Nat) : Nat := ((mv + 7) / 8) * 8
def u32VarBytes (mv : Nat) : Nat := ((4 * mv + 7) / 8) * 8
def whBytes (mv : Nat) : Nat := ((8 * mv + 7) / 8) * 8
def fixedBytes (mv : Nat) : Nat :=
  200 + valsBytes mv + markBytes mv + 4 * u32VarBytes mv + whBytes mv

theorem valsBytes_ge (mv : Nat) : 2 * mv ≤ valsBytes mv := by unfold valsBytes; omega
theorem markBytes_ge (mv : Nat) : mv ≤ markBytes mv := by unfold markBytes; omega
theorem u32VarBytes_ge (mv : Nat) : 4 * mv ≤ u32VarBytes mv := by unfold u32VarBytes; omega
theorem whBytes_ge (mv : Nat) : 8 * mv ≤ whBytes mv := by unfold whBytes; omega

theorem fixedBytes_lt {mv : Nat} (hmv : mv < dimacsBound) : fixedBytes mv < 2 ^ 34 := by
  unfold fixedBytes valsBytes markBytes u32VarBytes whBytes dimacsBound at *; omega

/-- Static arena geometry established by `kissat_init_state`. -/
structure ArenaCfg where
  hdr : BitVec 64
  avail : Nat
  mv : Nat
  nc : Nat
  max_c : Nat
  lcap : Nat
  hmv : mv < dimacsBound
  hnc : nc < dimacsBound
  hmax_c : max_c < dimacsBound
  hlcap : lcap < dimacsBound
  havail_fit : hdr.toNat + avail < 2 ^ 64
  hsize : fixedBytes mv + 24 * max_c + 4 * lcap ≤ avail

namespace ArenaCfg

def pVals (c : ArenaCfg) : BitVec 64 := c.hdr + BitVec.ofNat 64 200
def pMark (c : ArenaCfg) : BitVec 64 := c.pVals + BitVec.ofNat 64 (valsBytes c.mv)
def pLevel (c : ArenaCfg) : BitVec 64 := c.pMark + BitVec.ofNat 64 (markBytes c.mv)
def pReason (c : ArenaCfg) : BitVec 64 := c.pLevel + BitVec.ofNat 64 (u32VarBytes c.mv)
def pTrail (c : ArenaCfg) : BitVec 64 := c.pReason + BitVec.ofNat 64 (u32VarBytes c.mv)
def pTmp (c : ArenaCfg) : BitVec 64 := c.pTrail + BitVec.ofNat 64 (u32VarBytes c.mv)
def pWh (c : ArenaCfg) : BitVec 64 := c.pTmp + BitVec.ofNat 64 (u32VarBytes c.mv)
def pClauses (c : ArenaCfg) : BitVec 64 := c.pWh + BitVec.ofNat 64 (whBytes c.mv)
def pWn (c : ArenaCfg) : BitVec 64 := c.pClauses + BitVec.ofNat 64 (16 * c.max_c)
def pLpool (c : ArenaCfg) : BitVec 64 := c.pClauses + BitVec.ofNat 64 (24 * c.max_c)
def pSlack (c : ArenaCfg) : BitVec 64 := c.pLpool + BitVec.ofNat 64 (4 * c.lcap)
def slack (c : ArenaCfg) : Nat := c.avail - (fixedBytes c.mv + 24 * c.max_c + 4 * c.lcap)

/-- Combined static padding and trailing slack regions (never accessed after `init_state`). -/
def pad (c : ArenaCfg) : Mem 64 → Prop :=
  region (c.pVals + BitVec.ofNat 64 (2 * c.mv)) (valsBytes c.mv - 2 * c.mv) ⋆
  region (c.pMark + BitVec.ofNat 64 c.mv) (markBytes c.mv - c.mv) ⋆
  region (c.pLevel + BitVec.ofNat 64 (4 * c.mv)) (u32VarBytes c.mv - 4 * c.mv) ⋆
  region (c.pReason + BitVec.ofNat 64 (4 * c.mv)) (u32VarBytes c.mv - 4 * c.mv) ⋆
  region (c.pTrail + BitVec.ofNat 64 (4 * c.mv)) (u32VarBytes c.mv - 4 * c.mv) ⋆
  region (c.pTmp + BitVec.ofNat 64 (4 * c.mv)) (u32VarBytes c.mv - 4 * c.mv) ⋆
  region (c.pWh + BitVec.ofNat 64 (8 * c.mv)) (whBytes c.mv - 8 * c.mv) ⋆
  region c.pSlack c.slack

/-- Collapse all 12 active regions + static padding back into `region c.hdr c.avail`. -/
theorem regions_to_avail (c : ArenaCfg) {m : Mem 64}
    (hm : (region c.hdr 32 ⋆ region (c.hdr + BitVec.ofNat 64 32) 168 ⋆
      region c.pVals (2 * c.mv) ⋆ region c.pMark c.mv ⋆
      region c.pLevel (4 * c.mv) ⋆ region c.pReason (4 * c.mv) ⋆
      region c.pTrail (4 * c.mv) ⋆ region c.pTmp (4 * c.mv) ⋆
      region c.pWh (8 * c.mv) ⋆ region c.pClauses (16 * c.max_c) ⋆
      region c.pWn (8 * c.max_c) ⋆ region c.pLpool (4 * c.lcap) ⋆
      c.pad) m) : region c.hdr c.avail m := by
  have hfit := c.havail_fit
  have hsz := c.hsize
  have hv := valsBytes_ge c.mv; have hmk := markBytes_ge c.mv
  have hu := u32VarBytes_ge c.mv; have hw := whBytes_ge c.mv
  have hfx := fixedBytes_lt c.hmv
  unfold pad at hm
  have hm2 : ((region c.hdr 32 ⋆ region (c.hdr + BitVec.ofNat 64 32) 168) ⋆
      ((region c.pVals (2 * c.mv) ⋆
          region (c.pVals + BitVec.ofNat 64 (2 * c.mv)) (valsBytes c.mv - 2 * c.mv)) ⋆
      ((region c.pMark c.mv ⋆
          region (c.pMark + BitVec.ofNat 64 c.mv) (markBytes c.mv - c.mv)) ⋆
      ((region c.pLevel (4 * c.mv) ⋆
          region (c.pLevel + BitVec.ofNat 64 (4 * c.mv)) (u32VarBytes c.mv - 4 * c.mv)) ⋆
      ((region c.pReason (4 * c.mv) ⋆
          region (c.pReason + BitVec.ofNat 64 (4 * c.mv)) (u32VarBytes c.mv - 4 * c.mv)) ⋆
      ((region c.pTrail (4 * c.mv) ⋆
          region (c.pTrail + BitVec.ofNat 64 (4 * c.mv)) (u32VarBytes c.mv - 4 * c.mv)) ⋆
      ((region c.pTmp (4 * c.mv) ⋆
          region (c.pTmp + BitVec.ofNat 64 (4 * c.mv)) (u32VarBytes c.mv - 4 * c.mv)) ⋆
      ((region c.pWh (8 * c.mv) ⋆
          region (c.pWh + BitVec.ofNat 64 (8 * c.mv)) (whBytes c.mv - 8 * c.mv)) ⋆
      ((region c.pClauses (16 * c.max_c) ⋆ region c.pWn (8 * c.max_c)) ⋆
      (region c.pLpool (4 * c.lcap) ⋆ region c.pSlack c.slack)))))))))) m := sep_ac hm
  have hle : fixedBytes c.mv ≤ c.avail := by omega
  unfold fixedBytes at hsz hle
  rw [
    region_merge_eq (a := c.hdr) (n1 := 32) (n2 := 168) (n := 200) rfl (by decide),
    region_merge_eq (a := c.pVals) (n1 := 2 * c.mv) (n2 := valsBytes c.mv - 2 * c.mv)
      (n := valsBytes c.mv) (by omega) (by omega),
    region_merge_eq (a := c.pMark) (n1 := c.mv) (n2 := markBytes c.mv - c.mv)
      (n := markBytes c.mv) (by omega) (by omega),
    region_merge_eq (a := c.pLevel) (n1 := 4 * c.mv) (n2 := u32VarBytes c.mv - 4 * c.mv)
      (n := u32VarBytes c.mv) (by omega) (by omega),
    region_merge_eq (a := c.pReason) (n1 := 4 * c.mv) (n2 := u32VarBytes c.mv - 4 * c.mv)
      (n := u32VarBytes c.mv) (by omega) (by omega),
    region_merge_eq (a := c.pTrail) (n1 := 4 * c.mv) (n2 := u32VarBytes c.mv - 4 * c.mv)
      (n := u32VarBytes c.mv) (by omega) (by omega),
    region_merge_eq (a := c.pTmp) (n1 := 4 * c.mv) (n2 := u32VarBytes c.mv - 4 * c.mv)
      (n := u32VarBytes c.mv) (by omega) (by omega),
    region_merge_eq (a := c.pWh) (n1 := 8 * c.mv) (n2 := whBytes c.mv - 8 * c.mv)
      (n := whBytes c.mv) (by omega) (by omega),
    show c.pWn = c.pClauses + BitVec.ofNat 64 (16 * c.max_c) from rfl,
    region_merge_eq (a := c.pClauses) (n1 := 16 * c.max_c) (n2 := 8 * c.max_c)
      (n := 24 * c.max_c) (by omega) (by omega),
    show c.pSlack = c.pLpool + BitVec.ofNat 64 (4 * c.lcap) from rfl,
    region_merge_eq (a := c.pLpool) (n1 := 4 * c.lcap) (n2 := c.slack)
      (n := 4 * c.lcap + c.slack) rfl (by unfold slack fixedBytes; omega),
    show c.pLpool = c.pClauses + BitVec.ofNat 64 (24 * c.max_c) from rfl,
    region_merge_eq (a := c.pClauses) (n1 := 24 * c.max_c) (n2 := 4 * c.lcap + c.slack)
      (n := 24 * c.max_c + (4 * c.lcap + c.slack)) rfl (by unfold slack fixedBytes; omega),
    show c.pClauses = c.pWh + BitVec.ofNat 64 (whBytes c.mv) from rfl,
    region_merge_eq (a := c.pWh) (n1 := whBytes c.mv)
      (n2 := 24 * c.max_c + (4 * c.lcap + c.slack))
      (n := whBytes c.mv + (24 * c.max_c + (4 * c.lcap + c.slack))) rfl
      (by unfold slack fixedBytes; omega),
    show c.pWh = c.pTmp + BitVec.ofNat 64 (u32VarBytes c.mv) from rfl,
    region_merge_eq (a := c.pTmp) (n1 := u32VarBytes c.mv)
      (n2 := whBytes c.mv + (24 * c.max_c + (4 * c.lcap + c.slack)))
      (n := u32VarBytes c.mv + (whBytes c.mv + (24 * c.max_c + (4 * c.lcap + c.slack)))) rfl
      (by unfold slack fixedBytes; omega),
    show c.pTmp = c.pTrail + BitVec.ofNat 64 (u32VarBytes c.mv) from rfl,
    region_merge_eq (a := c.pTrail) (n1 := u32VarBytes c.mv)
      (n := u32VarBytes c.mv + (u32VarBytes c.mv +
        (whBytes c.mv + (24 * c.max_c + (4 * c.lcap + c.slack))))) rfl
      (by unfold slack fixedBytes; omega),
    show c.pTrail = c.pReason + BitVec.ofNat 64 (u32VarBytes c.mv) from rfl,
    region_merge_eq (a := c.pReason) (n1 := u32VarBytes c.mv)
      (n := u32VarBytes c.mv + (u32VarBytes c.mv + (u32VarBytes c.mv +
        (whBytes c.mv + (24 * c.max_c + (4 * c.lcap + c.slack)))))) rfl
      (by unfold slack fixedBytes; omega),
    show c.pReason = c.pLevel + BitVec.ofNat 64 (u32VarBytes c.mv) from rfl,
    region_merge_eq (a := c.pLevel) (n1 := u32VarBytes c.mv)
      (n := u32VarBytes c.mv + (u32VarBytes c.mv + (u32VarBytes c.mv + (u32VarBytes c.mv +
        (whBytes c.mv + (24 * c.max_c + (4 * c.lcap + c.slack))))))) rfl
      (by unfold slack fixedBytes; omega),
    show c.pLevel = c.pMark + BitVec.ofNat 64 (markBytes c.mv) from rfl,
    region_merge_eq (a := c.pMark) (n1 := markBytes c.mv)
      (n := markBytes c.mv + (u32VarBytes c.mv + (u32VarBytes c.mv + (u32VarBytes c.mv +
        (u32VarBytes c.mv + (whBytes c.mv + (24 * c.max_c + (4 * c.lcap + c.slack)))))))) rfl
      (by unfold slack fixedBytes; omega),
    show c.pMark = c.pVals + BitVec.ofNat 64 (valsBytes c.mv) from rfl,
    region_merge_eq (a := c.pVals) (n1 := valsBytes c.mv)
      (n := valsBytes c.mv + (markBytes c.mv + (u32VarBytes c.mv + (u32VarBytes c.mv +
        (u32VarBytes c.mv + (u32VarBytes c.mv + (whBytes c.mv +
          (24 * c.max_c + (4 * c.lcap + c.slack))))))))) rfl
      (by unfold slack fixedBytes; omega),
    show c.pVals = c.hdr + BitVec.ofNat 64 200 from rfl,
    region_merge_eq (a := c.hdr) (n1 := 200) (n := c.avail)
      (by unfold slack fixedBytes; omega) (by omega)] at hm2
  exact hm2

end ArenaCfg

/-- Dynamic logical state of the `KissatHdr` + all 10 arena sub-arrays. -/
structure ArenaState where
  d_cur : BitVec 64
  d_val : BitVec 64
  lit_len : Nat
  num_clauses : Nat
  trail_end : Nat
  propagated : Nat
  cur_level : Nat
  fuel : BitVec 64
  confl_cid : BitVec 64
  tmp_cnt : Nat
  tmp_len : Nat
  vals : List (BitVec 8)
  mrk : List (BitVec 8)
  lvl : List (BitVec 32)
  rsns : List (BitVec 32)
  trl : List (BitVec 32)
  tmp : List (BitVec 32)
  wh : List (BitVec 32)
  cls : List (BitVec 32)
  wn : List (BitVec 32)
  lpool : List (BitVec 32)

/-- Array-length and scalar-bound consistency of `ArenaState` against `ArenaCfg`. -/
structure ArenaState.LengthsOk (c : ArenaCfg) (s : ArenaState) : Prop where
  vals_len : s.vals.length = 2 * c.mv
  mrk_len : s.mrk.length = c.mv
  lvl_len : s.lvl.length = c.mv
  rsns_len : s.rsns.length = c.mv
  trl_len : s.trl.length = c.mv
  tmp_len_arr : s.tmp.length = c.mv
  wh_len : s.wh.length = 2 * c.mv
  cls_len : s.cls.length = 4 * c.max_c
  wn_len : s.wn.length = 2 * c.max_c
  lpool_len : s.lpool.length = c.lcap
  lit_len_le : s.lit_len ≤ c.lcap
  num_clauses_le : s.num_clauses ≤ c.max_c
  trail_end_le : s.trail_end ≤ c.mv
  propagated_le : s.propagated ≤ s.trail_end
  cur_level_lt : s.cur_level < 2 ^ 32
  tmp_cnt_lt : s.tmp_cnt < 2 ^ 64
  tmp_len_lt : s.tmp_len < 2 ^ 64

/-- The 21 `u64` words of `KissatHdr` after `KissatDimacs d` (offsets `32 .. 192`). -/
def hdrTailWords (c : ArenaCfg) (s : ArenaState) : List (BitVec 64) :=
  [ BitVec.ofNat 64 c.max_c,
    BitVec.ofNat 64 c.lcap,
    BitVec.ofNat 64 s.lit_len,
    BitVec.ofNat 64 s.num_clauses,
    c.pVals, c.pMark, c.pLevel, c.pReason, c.pTrail,
    c.pWh, c.pClauses, c.pWn, c.pLpool, c.pTmp,
    BitVec.ofNat 64 s.trail_end,
    BitVec.ofNat 64 s.propagated,
    BitVec.ofNat 64 s.cur_level,
    s.fuel,
    s.confl_cid,
    BitVec.ofNat 64 s.tmp_cnt,
    BitVec.ofNat 64 s.tmp_len ]

@[simp] theorem hdrTailWords_length (c : ArenaCfg) (s : ArenaState) :
    (hdrTailWords c s).length = 21 := rfl

/-- Spatial separation predicate for the entire partitioned Kissat arena at `c.hdr`. -/
def ArenaMem (c : ArenaCfg) (s : ArenaState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.d_cur s.d_val ⋆
  array64 (c.hdr + 32) (hdrTailWords c s) ⋆
  array (t := i8) c.pVals s.vals ⋆
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

/-- Combined arena invariant (`LengthsOk` + `ArenaMem`). -/
def ArenaInv (c : ArenaCfg) (s : ArenaState) : Mem 64 → Prop := fun m =>
  s.LengthsOk c ∧ ArenaMem c s m

/-- Collapse `ArenaMem` (with arbitrary `dimacsState` prefix, e.g. after `kissat_check_model`)
back into `region c.hdr c.avail`. -/
theorem arenaMem_anyDimacs_to_region {c : ArenaCfg} {s : ArenaState}
    {mv' nc' cur' val' : BitVec 64} {m : Mem 64} (hlen : s.LengthsOk c)
    (hm : (dimacsState c.hdr mv' nc' cur' val' ⋆
      array64 (c.hdr + 32) (hdrTailWords c s) ⋆
      array (t := i8) c.pVals s.vals ⋆
      array (t := i8) c.pMark s.mrk ⋆
      array (t := i32) c.pLevel s.lvl ⋆
      array (t := i32) c.pReason s.rsns ⋆
      array (t := i32) c.pTrail s.trl ⋆
      array (t := i32) c.pTmp s.tmp ⋆
      array (t := i32) c.pWh s.wh ⋆
      array (t := i32) c.pClauses s.cls ⋆
      array (t := i32) c.pWn s.wn ⋆
      array (t := i32) c.pLpool s.lpool ⋆
      c.pad) m) : region c.hdr c.avail m := by
  have hmv := c.hmv; have hmc := c.hmax_c; have hlc := c.hlcap
  unfold dimacsBound at hmv hmc hlc
  refine c.regions_to_avail ?_
  refine sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2
    (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2
      (fun _ h => dimacsState_to_region h)
      (fun _ h => by
        have h' := array_to_region (t := i64) (xs := hdrTailWords c s)
          (by simp [Ty.bytes, Ty.size, i64]) (by rwa [← array64_eq_array])
        simpa [Ty.bytes, Ty.size, i64] using h'))
      (fun _ h => by
        have h' := array_to_region (t := i8)
          (by simp [Ty.bytes, Ty.size, i8, hlen.vals_len]; omega) h
        simpa [Ty.bytes, Ty.size, i8, hlen.vals_len] using h'))
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
      (fun _ h => h) m hm

theorem ArenaInv.to_region {c : ArenaCfg} {s : ArenaState} {m : Mem 64}
    (h : ArenaInv c s m) : region c.hdr c.avail m :=
  arenaMem_anyDimacs_to_region h.1 h.2

/-- Re-merge aligned header region with leading alignment pad into `region work_ptr work_len`. -/
theorem pad_region_merge {work_ptr : BitVec 64} {pad avail : Nat} {m : Mem 64}
    (hfit : pad + avail ≤ 2 ^ 64)
    (hm : (region work_ptr pad ⋆ region (work_ptr + BitVec.ofNat 64 pad) avail) m) :
    region work_ptr (pad + avail) m := by
  rwa [region_merge_eq rfl hfit] at hm

/-! ## 4. Direct `ArenaMem` load / store / framing helpers -/

section ArenaAccess
variable {c : ArenaCfg} {s : ArenaState} {R : Mem 64 → Prop} {m : Mem 64}

/-- Rest of `ArenaMem` after factoring out `dimacsState c.hdr ...`. -/
def ArenaRest (c : ArenaCfg) (s : ArenaState) : Mem 64 → Prop :=
  array64 (c.hdr + 32) (hdrTailWords c s) ⋆
  array (t := i8) c.pVals s.vals ⋆
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

theorem arenaMem_eq_dimacs_sep (c : ArenaCfg) (s : ArenaState) :
    ArenaMem c s =
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.d_cur s.d_val ⋆
        ArenaRest c s) := by
  unfold ArenaMem ArenaRest; ac_rfl

theorem arenaRest_d_irrel (c : ArenaCfg) (s : ArenaState) (cur' val' : BitVec 64) :
    ArenaRest c { s with d_cur := cur', d_val := val' } = ArenaRest c s := rfl

private theorem arenaMem_focus_dimacs (hm : (ArenaMem c s ⋆ R) m) :
    (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.d_cur s.d_val ⋆
      (ArenaRest c s ⋆ R)) m := by
  rw [arenaMem_eq_dimacs_sep, sep_assoc] at hm; exact hm

private theorem arenaMem_unfocus_dimacs {cur' val' : BitVec 64} {m' : Mem 64}
    (hm : (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) cur' val' ⋆
      (ArenaRest c s ⋆ R)) m') :
    (ArenaMem c { s with d_cur := cur', d_val := val' } ⋆ R) m' := by
  rw [arenaMem_eq_dimacs_sep, arenaRest_d_irrel, sep_assoc]; exact hm

/-- Generic array-focusing helper for `ArenaMem` (avoids repeated 13-term `ac_rfl`). -/
private theorem load_hdr_tail (i : Nat) (hi : i < 21) (hm : (ArenaMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + BitVec.ofNat 64 (32 + 8 * i)) =
      some ((hdrTailWords c s)[i]'(by simpa using hi)) := by
  have h1 : (array64 (c.hdr + 32) (hdrTailWords c s) ⋆
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.d_cur s.d_val ⋆
        array (t := i8) c.pVals s.vals ⋆ array (t := i8) c.pMark s.mrk ⋆
        array (t := i32) c.pLevel s.lvl ⋆ array (t := i32) c.pReason s.rsns ⋆
        array (t := i32) c.pTrail s.trl ⋆ array (t := i32) c.pTmp s.tmp ⋆
        array (t := i32) c.pWh s.wh ⋆ array (t := i32) c.pClauses s.cls ⋆
        array (t := i32) c.pWn s.wn ⋆ array (t := i32) c.pLpool s.lpool ⋆ c.pad ⋆ R)) m := by
    unfold ArenaMem at hm; exact sep_ac hm
  have hload := loadVal_array64 (i := i) (by simpa using hi) h1
  rwa [show c.hdr + (32 : BitVec 64) + BitVec.ofNat 64 (8 * i) =
    c.hdr + BitVec.ofNat 64 (32 + 8 * i) from ptr_add_ofNat c.hdr 32 (8 * i)] at hload

private theorem store_hdr_tail (i : Nat) (hi : i < 21) (v : BitVec 64) (s' : ArenaState)
    (hm : (ArenaMem c s ⋆ R) m)
    (heq : hdrTailWords c s' = (hdrTailWords c s).set i v)
    (hdcur : s'.d_cur = s.d_cur) (hdval : s'.d_val = s.d_val)
    (hvals : s'.vals = s.vals) (hmrk : s'.mrk = s.mrk)
    (hlvl : s'.lvl = s.lvl) (hrsns : s'.rsns = s.rsns)
    (htrl : s'.trl = s.trl) (htmp : s'.tmp = s.tmp)
    (hwh : s'.wh = s.wh) (hcls : s'.cls = s.cls)
    (hwn : s'.wn = s.wn) (hlpool : s'.lpool = s.lpool) :
    storeOk m i64 (c.hdr + BitVec.ofNat 64 (32 + 8 * i)) ∧
      (ArenaMem c s' ⋆ R) (storeMem m i64 (c.hdr + BitVec.ofNat 64 (32 + 8 * i)) v) := by
  have h1 : (array64 (c.hdr + 32) (hdrTailWords c s) ⋆
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.d_cur s.d_val ⋆
        array (t := i8) c.pVals s.vals ⋆ array (t := i8) c.pMark s.mrk ⋆
        array (t := i32) c.pLevel s.lvl ⋆ array (t := i32) c.pReason s.rsns ⋆
        array (t := i32) c.pTrail s.trl ⋆ array (t := i32) c.pTmp s.tmp ⋆
        array (t := i32) c.pWh s.wh ⋆ array (t := i32) c.pClauses s.cls ⋆
        array (t := i32) c.pWn s.wn ⋆ array (t := i32) c.pLpool s.lpool ⋆ c.pad ⋆ R)) m := by
    unfold ArenaMem at hm; exact sep_ac hm
  obtain ⟨hok, hst⟩ := store_array64 (i := i) v (by simpa using hi) h1
  rw [show c.hdr + (32 : BitVec 64) + BitVec.ofNat 64 (8 * i) =
    c.hdr + BitVec.ofNat 64 (32 + 8 * i) from ptr_add_ofNat c.hdr 32 (8 * i)] at hok hst
  refine ⟨hok, ?_⟩
  rw [← heq] at hst
  unfold ArenaMem
  rw [hdcur, hdval, hvals, hmrk, hlvl, hrsns, htrl, htmp, hwh, hcls, hwn, hlpool]
  exact sep_ac hst

theorem load_arena_mv (hm : (ArenaMem c s ⋆ R) m) :
    loadVal m i64 c.hdr = some (BitVec.ofNat 64 c.mv) :=
  load_dimacs_mv (arenaMem_focus_dimacs hm)

theorem load_arena_nc (hm : (ArenaMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 8) = some (BitVec.ofNat 64 c.nc) :=
  load_dimacs_nc (arenaMem_focus_dimacs hm)

theorem load_arena_cur (hm : (ArenaMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 16) = some s.d_cur :=
  load_dimacs_cur (arenaMem_focus_dimacs hm)

theorem load_arena_val (hm : (ArenaMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 24) = some s.d_val :=
  load_dimacs_val (arenaMem_focus_dimacs hm)

theorem store_arena_cur (v : BitVec 64) (hm : (ArenaMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 16) ∧
      (ArenaMem c { s with d_cur := v } ⋆ R) (storeMem m i64 (c.hdr + 16) v) := by
  obtain ⟨hok, hst⟩ := store_dimacs_cur v (arenaMem_focus_dimacs hm)
  exact ⟨hok, arenaMem_unfocus_dimacs hst⟩

theorem load_arena_max_clauses (hm : (ArenaMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 32) = some (BitVec.ofNat 64 c.max_c) := load_hdr_tail 0 (by decide) hm
theorem load_arena_lit_cap (hm : (ArenaMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 40) = some (BitVec.ofNat 64 c.lcap) := load_hdr_tail 1 (by decide) hm
theorem load_arena_lit_len (hm : (ArenaMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 48) = some (BitVec.ofNat 64 s.lit_len) := load_hdr_tail 2 (by decide) hm
theorem load_arena_num_clauses (hm : (ArenaMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 56) = some (BitVec.ofNat 64 s.num_clauses) :=
  load_hdr_tail 3 (by decide) hm
theorem load_arena_values (hm : (ArenaMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 64) = some c.pVals := load_hdr_tail 4 (by decide) hm
theorem load_arena_mark (hm : (ArenaMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 72) = some c.pMark := load_hdr_tail 5 (by decide) hm
theorem load_arena_level (hm : (ArenaMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 80) = some c.pLevel := load_hdr_tail 6 (by decide) hm
theorem load_arena_reason (hm : (ArenaMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 88) = some c.pReason := load_hdr_tail 7 (by decide) hm
theorem load_arena_trail (hm : (ArenaMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 96) = some c.pTrail := load_hdr_tail 8 (by decide) hm
theorem load_arena_watch_head (hm : (ArenaMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 104) = some c.pWh := load_hdr_tail 9 (by decide) hm
theorem load_arena_clauses (hm : (ArenaMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 112) = some c.pClauses := load_hdr_tail 10 (by decide) hm
theorem load_arena_watch_next (hm : (ArenaMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 120) = some c.pWn := load_hdr_tail 11 (by decide) hm
theorem load_arena_lit_pool (hm : (ArenaMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 128) = some c.pLpool := load_hdr_tail 12 (by decide) hm
theorem load_arena_tmp_lits (hm : (ArenaMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 136) = some c.pTmp := load_hdr_tail 13 (by decide) hm
theorem load_arena_trail_end (hm : (ArenaMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 144) = some (BitVec.ofNat 64 s.trail_end) :=
  load_hdr_tail 14 (by decide) hm
theorem load_arena_propagated (hm : (ArenaMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 152) = some (BitVec.ofNat 64 s.propagated) :=
  load_hdr_tail 15 (by decide) hm
theorem load_arena_cur_level (hm : (ArenaMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 160) = some (BitVec.ofNat 64 s.cur_level) :=
  load_hdr_tail 16 (by decide) hm
theorem load_arena_fuel (hm : (ArenaMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 168) = some s.fuel := load_hdr_tail 17 (by decide) hm
theorem load_arena_confl_cid (hm : (ArenaMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 176) = some s.confl_cid := load_hdr_tail 18 (by decide) hm
theorem load_arena_tmp_cnt (hm : (ArenaMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 184) = some (BitVec.ofNat 64 s.tmp_cnt) :=
  load_hdr_tail 19 (by decide) hm
theorem load_arena_tmp_len (hm : (ArenaMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 192) = some (BitVec.ofNat 64 s.tmp_len) :=
  load_hdr_tail 20 (by decide) hm

theorem store_arena_lit_len (v : Nat) (hm : (ArenaMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 48) ∧ (ArenaMem c { s with lit_len := v } ⋆ R)
      (storeMem m i64 (c.hdr + 48) (BitVec.ofNat 64 v)) :=
  store_hdr_tail 2 (by decide) _ _ hm rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

theorem store_arena_num_clauses (v : Nat) (hm : (ArenaMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 56) ∧ (ArenaMem c { s with num_clauses := v } ⋆ R)
      (storeMem m i64 (c.hdr + 56) (BitVec.ofNat 64 v)) :=
  store_hdr_tail 3 (by decide) _ _ hm rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

theorem store_arena_trail_end (v : Nat) (hm : (ArenaMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 144) ∧ (ArenaMem c { s with trail_end := v } ⋆ R)
      (storeMem m i64 (c.hdr + 144) (BitVec.ofNat 64 v)) :=
  store_hdr_tail 14 (by decide) _ _ hm rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

theorem store_arena_propagated (v : Nat) (hm : (ArenaMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 152) ∧ (ArenaMem c { s with propagated := v } ⋆ R)
      (storeMem m i64 (c.hdr + 152) (BitVec.ofNat 64 v)) :=
  store_hdr_tail 15 (by decide) _ _ hm rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

theorem store_arena_cur_level (v : Nat) (hm : (ArenaMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 160) ∧ (ArenaMem c { s with cur_level := v } ⋆ R)
      (storeMem m i64 (c.hdr + 160) (BitVec.ofNat 64 v)) :=
  store_hdr_tail 16 (by decide) _ _ hm rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

theorem store_arena_fuel (v : BitVec 64) (hm : (ArenaMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 168) ∧ (ArenaMem c { s with fuel := v } ⋆ R)
      (storeMem m i64 (c.hdr + 168) v) :=
  store_hdr_tail 17 (by decide) _ _ hm rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

theorem store_arena_confl_cid (v : BitVec 64) (hm : (ArenaMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 176) ∧ (ArenaMem c { s with confl_cid := v } ⋆ R)
      (storeMem m i64 (c.hdr + 176) v) :=
  store_hdr_tail 18 (by decide) _ _ hm rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

theorem store_arena_tmp_cnt (v : Nat) (hm : (ArenaMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 184) ∧ (ArenaMem c { s with tmp_cnt := v } ⋆ R)
      (storeMem m i64 (c.hdr + 184) (BitVec.ofNat 64 v)) :=
  store_hdr_tail 19 (by decide) _ _ hm rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

theorem store_arena_tmp_len (v : Nat) (hm : (ArenaMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 192) ∧ (ArenaMem c { s with tmp_len := v } ⋆ R)
      (storeMem m i64 (c.hdr + 192) (BitVec.ofNat 64 v)) :=
  store_hdr_tail 20 (by decide) _ _ hm rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-- Generic 1-step sub-array load/store wrapper eliminating repeated `ac_rfl` boilerplate. -/
private theorem load_arr_i8 {a : BitVec 64} {xs : List (BitVec 8)} {F : Mem 64 → Prop} {i : Nat}
    (hi : i < xs.length) (h : (array (t := i8) a xs ⋆ F) m) :
    loadVal m i8 (a + BitVec.ofNat 64 i) = some xs[i] := by
  simpa [Ty.bytes, Ty.size, i8] using loadVal_array (t := i8) (by decide) hi h

private theorem store_arr_i8 {a : BitVec 64} {xs : List (BitVec 8)} {F : Mem 64 → Prop} {i : Nat}
    (v : BitVec 8) (hi : i < xs.length) (h : (array (t := i8) a xs ⋆ F) m) :
    storeOk m i8 (a + BitVec.ofNat 64 i) ∧
      (array (t := i8) a (xs.set i v) ⋆ F) (storeMem m i8 (a + BitVec.ofNat 64 i) v) := by
  simpa [Ty.bytes, Ty.size, i8] using store_array (t := i8) v (by decide) hi h

private theorem load_arr_i32 {a : BitVec 64} {xs : List (BitVec 32)} {F : Mem 64 → Prop} {i : Nat}
    (hi : i < xs.length) (h : (array (t := i32) a xs ⋆ F) m) :
    loadVal m i32 (a + BitVec.ofNat 64 (4 * i)) = some xs[i] :=
  loadVal_array (t := i32) (by decide) hi h

private theorem store_arr_i32 {a : BitVec 64} {xs : List (BitVec 32)} {F : Mem 64 → Prop}
    {i : Nat} (v : BitVec 32) (hi : i < xs.length) (h : (array (t := i32) a xs ⋆ F) m) :
    storeOk m i32 (a + BitVec.ofNat 64 (4 * i)) ∧
      (array (t := i32) a (xs.set i v) ⋆ F) (storeMem m i32 (a + BitVec.ofNat 64 (4 * i)) v) :=
  store_array (t := i32) v (by decide) hi h

private def hdrHead (c : ArenaCfg) (s : ArenaState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.d_cur s.d_val ⋆
  array64 (c.hdr + 32) (hdrTailWords c s) ⋆ c.pad

private theorem arenaMem_eq_head (c : ArenaCfg) (s : ArenaState) :
    ArenaMem c s =
      (hdrHead c s ⋆ array (t := i8) c.pVals s.vals ⋆ array (t := i8) c.pMark s.mrk ⋆
        array (t := i32) c.pLevel s.lvl ⋆ array (t := i32) c.pReason s.rsns ⋆
        array (t := i32) c.pTrail s.trl ⋆ array (t := i32) c.pTmp s.tmp ⋆
        array (t := i32) c.pWh s.wh ⋆ array (t := i32) c.pClauses s.cls ⋆
        array (t := i32) c.pWn s.wn ⋆ array (t := i32) c.pLpool s.lpool) := by
  unfold ArenaMem hdrHead; ac_rfl

private theorem arenaMem_focus_vals (hm : (ArenaMem c s ⋆ R) m) :
    (array (t := i8) c.pVals s.vals ⋆
      (hdrHead c s ⋆ array (t := i8) c.pMark s.mrk ⋆ array (t := i32) c.pLevel s.lvl ⋆
        array (t := i32) c.pReason s.rsns ⋆ array (t := i32) c.pTrail s.trl ⋆
        array (t := i32) c.pTmp s.tmp ⋆ array (t := i32) c.pWh s.wh ⋆
        array (t := i32) c.pClauses s.cls ⋆ array (t := i32) c.pWn s.wn ⋆
        array (t := i32) c.pLpool s.lpool ⋆ R)) m := by
  rw [arenaMem_eq_head] at hm; exact sep_ac hm

theorem load_arena_vals {i : Nat} (hi : i < s.vals.length) (hm : (ArenaMem c s ⋆ R) m) :
    loadVal m i8 (c.pVals + BitVec.ofNat 64 i) = some s.vals[i] :=
  load_arr_i8 hi (arenaMem_focus_vals hm)

theorem store_arena_vals {i : Nat} (v : BitVec 8) (hi : i < s.vals.length)
    (hm : (ArenaMem c s ⋆ R) m) :
    storeOk m i8 (c.pVals + BitVec.ofNat 64 i) ∧
      (ArenaMem c { s with vals := s.vals.set i v } ⋆ R)
        (storeMem m i8 (c.pVals + BitVec.ofNat 64 i) v) := by
  obtain ⟨hok, hst⟩ := store_arr_i8 v hi (arenaMem_focus_vals hm)
  exact ⟨hok, by rw [arenaMem_eq_head]; exact sep_ac hst⟩

private theorem arenaMem_focus_mrk (hm : (ArenaMem c s ⋆ R) m) :
    (array (t := i8) c.pMark s.mrk ⋆
      (hdrHead c s ⋆ array (t := i8) c.pVals s.vals ⋆ array (t := i32) c.pLevel s.lvl ⋆
        array (t := i32) c.pReason s.rsns ⋆ array (t := i32) c.pTrail s.trl ⋆
        array (t := i32) c.pTmp s.tmp ⋆ array (t := i32) c.pWh s.wh ⋆
        array (t := i32) c.pClauses s.cls ⋆ array (t := i32) c.pWn s.wn ⋆
        array (t := i32) c.pLpool s.lpool ⋆ R)) m := by
  rw [arenaMem_eq_head] at hm; exact sep_ac hm

theorem load_arena_mrk {i : Nat} (hi : i < s.mrk.length) (hm : (ArenaMem c s ⋆ R) m) :
    loadVal m i8 (c.pMark + BitVec.ofNat 64 i) = some s.mrk[i] :=
  load_arr_i8 hi (arenaMem_focus_mrk hm)

theorem store_arena_mrk {i : Nat} (v : BitVec 8) (hi : i < s.mrk.length)
    (hm : (ArenaMem c s ⋆ R) m) :
    storeOk m i8 (c.pMark + BitVec.ofNat 64 i) ∧
      (ArenaMem c { s with mrk := s.mrk.set i v } ⋆ R)
        (storeMem m i8 (c.pMark + BitVec.ofNat 64 i) v) := by
  obtain ⟨hok, hst⟩ := store_arr_i8 v hi (arenaMem_focus_mrk hm)
  exact ⟨hok, by rw [arenaMem_eq_head]; exact sep_ac hst⟩

private theorem arenaMem_focus_lvl (hm : (ArenaMem c s ⋆ R) m) :
    (array (t := i32) c.pLevel s.lvl ⋆
      (hdrHead c s ⋆ array (t := i8) c.pVals s.vals ⋆ array (t := i8) c.pMark s.mrk ⋆
        array (t := i32) c.pReason s.rsns ⋆ array (t := i32) c.pTrail s.trl ⋆
        array (t := i32) c.pTmp s.tmp ⋆ array (t := i32) c.pWh s.wh ⋆
        array (t := i32) c.pClauses s.cls ⋆ array (t := i32) c.pWn s.wn ⋆
        array (t := i32) c.pLpool s.lpool ⋆ R)) m := by
  rw [arenaMem_eq_head] at hm; exact sep_ac hm

theorem load_arena_lvl {i : Nat} (hi : i < s.lvl.length) (hm : (ArenaMem c s ⋆ R) m) :
    loadVal m i32 (c.pLevel + BitVec.ofNat 64 (4 * i)) = some s.lvl[i] :=
  load_arr_i32 hi (arenaMem_focus_lvl hm)

theorem store_arena_lvl {i : Nat} (v : BitVec 32) (hi : i < s.lvl.length)
    (hm : (ArenaMem c s ⋆ R) m) :
    storeOk m i32 (c.pLevel + BitVec.ofNat 64 (4 * i)) ∧
      (ArenaMem c { s with lvl := s.lvl.set i v } ⋆ R)
        (storeMem m i32 (c.pLevel + BitVec.ofNat 64 (4 * i)) v) := by
  obtain ⟨hok, hst⟩ := store_arr_i32 v hi (arenaMem_focus_lvl hm)
  exact ⟨hok, by rw [arenaMem_eq_head]; exact sep_ac hst⟩

private theorem arenaMem_focus_rsns (hm : (ArenaMem c s ⋆ R) m) :
    (array (t := i32) c.pReason s.rsns ⋆
      (hdrHead c s ⋆ array (t := i8) c.pVals s.vals ⋆ array (t := i8) c.pMark s.mrk ⋆
        array (t := i32) c.pLevel s.lvl ⋆ array (t := i32) c.pTrail s.trl ⋆
        array (t := i32) c.pTmp s.tmp ⋆ array (t := i32) c.pWh s.wh ⋆
        array (t := i32) c.pClauses s.cls ⋆ array (t := i32) c.pWn s.wn ⋆
        array (t := i32) c.pLpool s.lpool ⋆ R)) m := by
  rw [arenaMem_eq_head] at hm; exact sep_ac hm

theorem load_arena_rsns {i : Nat} (hi : i < s.rsns.length) (hm : (ArenaMem c s ⋆ R) m) :
    loadVal m i32 (c.pReason + BitVec.ofNat 64 (4 * i)) = some s.rsns[i] :=
  load_arr_i32 hi (arenaMem_focus_rsns hm)

theorem store_arena_rsns {i : Nat} (v : BitVec 32) (hi : i < s.rsns.length)
    (hm : (ArenaMem c s ⋆ R) m) :
    storeOk m i32 (c.pReason + BitVec.ofNat 64 (4 * i)) ∧
      (ArenaMem c { s with rsns := s.rsns.set i v } ⋆ R)
        (storeMem m i32 (c.pReason + BitVec.ofNat 64 (4 * i)) v) := by
  obtain ⟨hok, hst⟩ := store_arr_i32 v hi (arenaMem_focus_rsns hm)
  exact ⟨hok, by rw [arenaMem_eq_head]; exact sep_ac hst⟩

private theorem arenaMem_focus_trl (hm : (ArenaMem c s ⋆ R) m) :
    (array (t := i32) c.pTrail s.trl ⋆
      (hdrHead c s ⋆ array (t := i8) c.pVals s.vals ⋆ array (t := i8) c.pMark s.mrk ⋆
        array (t := i32) c.pLevel s.lvl ⋆ array (t := i32) c.pReason s.rsns ⋆
        array (t := i32) c.pTmp s.tmp ⋆ array (t := i32) c.pWh s.wh ⋆
        array (t := i32) c.pClauses s.cls ⋆ array (t := i32) c.pWn s.wn ⋆
        array (t := i32) c.pLpool s.lpool ⋆ R)) m := by
  rw [arenaMem_eq_head] at hm; exact sep_ac hm

theorem load_arena_trl {i : Nat} (hi : i < s.trl.length) (hm : (ArenaMem c s ⋆ R) m) :
    loadVal m i32 (c.pTrail + BitVec.ofNat 64 (4 * i)) = some s.trl[i] :=
  load_arr_i32 hi (arenaMem_focus_trl hm)

theorem store_arena_trl {i : Nat} (v : BitVec 32) (hi : i < s.trl.length)
    (hm : (ArenaMem c s ⋆ R) m) :
    storeOk m i32 (c.pTrail + BitVec.ofNat 64 (4 * i)) ∧
      (ArenaMem c { s with trl := s.trl.set i v } ⋆ R)
        (storeMem m i32 (c.pTrail + BitVec.ofNat 64 (4 * i)) v) := by
  obtain ⟨hok, hst⟩ := store_arr_i32 v hi (arenaMem_focus_trl hm)
  exact ⟨hok, by rw [arenaMem_eq_head]; exact sep_ac hst⟩

private theorem arenaMem_focus_tmp (hm : (ArenaMem c s ⋆ R) m) :
    (array (t := i32) c.pTmp s.tmp ⋆
      (hdrHead c s ⋆ array (t := i8) c.pVals s.vals ⋆ array (t := i8) c.pMark s.mrk ⋆
        array (t := i32) c.pLevel s.lvl ⋆ array (t := i32) c.pReason s.rsns ⋆
        array (t := i32) c.pTrail s.trl ⋆ array (t := i32) c.pWh s.wh ⋆
        array (t := i32) c.pClauses s.cls ⋆ array (t := i32) c.pWn s.wn ⋆
        array (t := i32) c.pLpool s.lpool ⋆ R)) m := by
  rw [arenaMem_eq_head] at hm; exact sep_ac hm

theorem load_arena_tmp {i : Nat} (hi : i < s.tmp.length) (hm : (ArenaMem c s ⋆ R) m) :
    loadVal m i32 (c.pTmp + BitVec.ofNat 64 (4 * i)) = some s.tmp[i] :=
  load_arr_i32 hi (arenaMem_focus_tmp hm)

theorem store_arena_tmp {i : Nat} (v : BitVec 32) (hi : i < s.tmp.length)
    (hm : (ArenaMem c s ⋆ R) m) :
    storeOk m i32 (c.pTmp + BitVec.ofNat 64 (4 * i)) ∧
      (ArenaMem c { s with tmp := s.tmp.set i v } ⋆ R)
        (storeMem m i32 (c.pTmp + BitVec.ofNat 64 (4 * i)) v) := by
  obtain ⟨hok, hst⟩ := store_arr_i32 v hi (arenaMem_focus_tmp hm)
  exact ⟨hok, by rw [arenaMem_eq_head]; exact sep_ac hst⟩

private theorem arenaMem_focus_wh (hm : (ArenaMem c s ⋆ R) m) :
    (array (t := i32) c.pWh s.wh ⋆
      (hdrHead c s ⋆ array (t := i8) c.pVals s.vals ⋆ array (t := i8) c.pMark s.mrk ⋆
        array (t := i32) c.pLevel s.lvl ⋆ array (t := i32) c.pReason s.rsns ⋆
        array (t := i32) c.pTrail s.trl ⋆ array (t := i32) c.pTmp s.tmp ⋆
        array (t := i32) c.pClauses s.cls ⋆ array (t := i32) c.pWn s.wn ⋆
        array (t := i32) c.pLpool s.lpool ⋆ R)) m := by
  rw [arenaMem_eq_head] at hm; exact sep_ac hm

theorem load_arena_wh {i : Nat} (hi : i < s.wh.length) (hm : (ArenaMem c s ⋆ R) m) :
    loadVal m i32 (c.pWh + BitVec.ofNat 64 (4 * i)) = some s.wh[i] :=
  load_arr_i32 hi (arenaMem_focus_wh hm)

theorem store_arena_wh {i : Nat} (v : BitVec 32) (hi : i < s.wh.length)
    (hm : (ArenaMem c s ⋆ R) m) :
    storeOk m i32 (c.pWh + BitVec.ofNat 64 (4 * i)) ∧
      (ArenaMem c { s with wh := s.wh.set i v } ⋆ R)
        (storeMem m i32 (c.pWh + BitVec.ofNat 64 (4 * i)) v) := by
  obtain ⟨hok, hst⟩ := store_arr_i32 v hi (arenaMem_focus_wh hm)
  exact ⟨hok, by rw [arenaMem_eq_head]; exact sep_ac hst⟩

private theorem arenaMem_focus_cls (hm : (ArenaMem c s ⋆ R) m) :
    (array (t := i32) c.pClauses s.cls ⋆
      (hdrHead c s ⋆ array (t := i8) c.pVals s.vals ⋆ array (t := i8) c.pMark s.mrk ⋆
        array (t := i32) c.pLevel s.lvl ⋆ array (t := i32) c.pReason s.rsns ⋆
        array (t := i32) c.pTrail s.trl ⋆ array (t := i32) c.pTmp s.tmp ⋆
        array (t := i32) c.pWh s.wh ⋆ array (t := i32) c.pWn s.wn ⋆
        array (t := i32) c.pLpool s.lpool ⋆ R)) m := by
  rw [arenaMem_eq_head] at hm; exact sep_ac hm

theorem load_arena_cls {i : Nat} (hi : i < s.cls.length) (hm : (ArenaMem c s ⋆ R) m) :
    loadVal m i32 (c.pClauses + BitVec.ofNat 64 (4 * i)) = some s.cls[i] :=
  load_arr_i32 hi (arenaMem_focus_cls hm)

theorem store_arena_cls {i : Nat} (v : BitVec 32) (hi : i < s.cls.length)
    (hm : (ArenaMem c s ⋆ R) m) :
    storeOk m i32 (c.pClauses + BitVec.ofNat 64 (4 * i)) ∧
      (ArenaMem c { s with cls := s.cls.set i v } ⋆ R)
        (storeMem m i32 (c.pClauses + BitVec.ofNat 64 (4 * i)) v) := by
  obtain ⟨hok, hst⟩ := store_arr_i32 v hi (arenaMem_focus_cls hm)
  exact ⟨hok, by rw [arenaMem_eq_head]; exact sep_ac hst⟩

private theorem arenaMem_focus_wn (hm : (ArenaMem c s ⋆ R) m) :
    (array (t := i32) c.pWn s.wn ⋆
      (hdrHead c s ⋆ array (t := i8) c.pVals s.vals ⋆ array (t := i8) c.pMark s.mrk ⋆
        array (t := i32) c.pLevel s.lvl ⋆ array (t := i32) c.pReason s.rsns ⋆
        array (t := i32) c.pTrail s.trl ⋆ array (t := i32) c.pTmp s.tmp ⋆
        array (t := i32) c.pWh s.wh ⋆ array (t := i32) c.pClauses s.cls ⋆
        array (t := i32) c.pLpool s.lpool ⋆ R)) m := by
  rw [arenaMem_eq_head] at hm; exact sep_ac hm

theorem load_arena_wn {i : Nat} (hi : i < s.wn.length) (hm : (ArenaMem c s ⋆ R) m) :
    loadVal m i32 (c.pWn + BitVec.ofNat 64 (4 * i)) = some s.wn[i] :=
  load_arr_i32 hi (arenaMem_focus_wn hm)

theorem store_arena_wn {i : Nat} (v : BitVec 32) (hi : i < s.wn.length)
    (hm : (ArenaMem c s ⋆ R) m) :
    storeOk m i32 (c.pWn + BitVec.ofNat 64 (4 * i)) ∧
      (ArenaMem c { s with wn := s.wn.set i v } ⋆ R)
        (storeMem m i32 (c.pWn + BitVec.ofNat 64 (4 * i)) v) := by
  obtain ⟨hok, hst⟩ := store_arr_i32 v hi (arenaMem_focus_wn hm)
  exact ⟨hok, by rw [arenaMem_eq_head]; exact sep_ac hst⟩

private theorem arenaMem_focus_lpool (hm : (ArenaMem c s ⋆ R) m) :
    (array (t := i32) c.pLpool s.lpool ⋆
      (hdrHead c s ⋆ array (t := i8) c.pVals s.vals ⋆ array (t := i8) c.pMark s.mrk ⋆
        array (t := i32) c.pLevel s.lvl ⋆ array (t := i32) c.pReason s.rsns ⋆
        array (t := i32) c.pTrail s.trl ⋆ array (t := i32) c.pTmp s.tmp ⋆
        array (t := i32) c.pWh s.wh ⋆ array (t := i32) c.pClauses s.cls ⋆
        array (t := i32) c.pWn s.wn ⋆ R)) m := by
  rw [arenaMem_eq_head] at hm; exact sep_ac hm

theorem load_arena_lpool {i : Nat} (hi : i < s.lpool.length) (hm : (ArenaMem c s ⋆ R) m) :
    loadVal m i32 (c.pLpool + BitVec.ofNat 64 (4 * i)) = some s.lpool[i] :=
  load_arr_i32 hi (arenaMem_focus_lpool hm)

theorem store_arena_lpool {i : Nat} (v : BitVec 32) (hi : i < s.lpool.length)
    (hm : (ArenaMem c s ⋆ R) m) :
    storeOk m i32 (c.pLpool + BitVec.ofNat 64 (4 * i)) ∧
      (ArenaMem c { s with lpool := s.lpool.set i v } ⋆ R)
        (storeMem m i32 (c.pLpool + BitVec.ofNat 64 (4 * i)) v) := by
  obtain ⟨hok, hst⟩ := store_arr_i32 v hi (arenaMem_focus_lpool hm)
  exact ⟨hok, by rw [arenaMem_eq_head]; exact sep_ac hst⟩

end ArenaAccess

end LeanQbe.T.Examples.Kissat
